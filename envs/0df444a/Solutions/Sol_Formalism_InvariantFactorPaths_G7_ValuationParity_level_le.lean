-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.ValuationParity.level_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:44:58.728024+00:00
-- url     : https://prove2.me/submissions/2ec217e9-e3f4-4731-9fc4-2990a4a113ac

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EntryAOneParity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral jetPair mfact)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
open Formalism.InvariantFactorPaths.G7.ValuationParity
namespace Formalism.InvariantFactorPaths.G7.ValuationParity
theorem _root_.solution {ν r0 r1 E : ℕ} [NeZero ν] (p : ℕ) (e : TpV ν r1 → ℕ) (α : PhiI ν r0 r1 E → ℕ)
    (β : KapI ν r1 E →₀ ℕ)
    (hτ : ∀ τ, ∑ φ, α φ * dAof p φ τ + ∑ k, β k * dBof p k τ ≤ e τ)
    (c : PhiI ν r0 r1 E → ZMod (2 * ν) × ℕ)
    (hc : ∀ φ, p ^ (2 * (c φ).2 + 1) ≤ dAof p φ ((c φ).1, φ.2.2.2.2)) (s : ZMod (2 * ν)) (e' : ℕ) :
    p ^ (2 * e' + 1) * ((∑ φ, if c φ = (s, e') then α φ else 0) +
      ∑ k : KapI ν r1 E, if (k.1, k.2.1.val) = (s, e') then β k else 0) ≤ alN e s := by
  have hφ : ∀ φ, (if c φ = (s, e') then p ^ (2 * e' + 1) * α φ else 0) ≤
      ∑ b, α φ * dAof p φ (s, b) := by
    intro φ
    split_ifs with h
    · have h1 := hc φ
      simp only [h] at h1
      calc p ^ (2 * e' + 1) * α φ = α φ * p ^ (2 * e' + 1) := mul_comm _ _
        _ ≤ α φ * dAof p φ (s, φ.2.2.2.2) := Nat.mul_le_mul_left _ h1
        _ ≤ ∑ b, α φ * dAof p φ (s, b) :=
          Finset.single_le_sum (f := fun b => α φ * dAof p φ (s, b)) (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ _)
    · exact Nat.zero_le _
  have hk : ∀ k : KapI ν r1 E, (if (k.1, k.2.1.val) = (s, e') then p ^ (2 * e' + 1) * β k else 0) ≤
      ∑ b, β k * dBof p k (s, b) := by
    intro k
    split_ifs with h
    · simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      calc p ^ (2 * e' + 1) * β k = β k * dBof p k (s, k.2.2) := by
            rw [← h1, ← h2]
            simp [dBof, mul_comm]
        _ ≤ ∑ b, β k * dBof p k (s, b) :=
          Finset.single_le_sum (f := fun b => β k * dBof p k (s, b)) (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ _)
    · exact Nat.zero_le _
  calc p ^ (2 * e' + 1) * ((∑ φ, if c φ = (s, e') then α φ else 0) +
        ∑ k : KapI ν r1 E, if (k.1, k.2.1.val) = (s, e') then β k else 0)
      = (∑ φ, if c φ = (s, e') then p ^ (2 * e' + 1) * α φ else 0) +
        ∑ k : KapI ν r1 E, (if (k.1, k.2.1.val) = (s, e') then p ^ (2 * e' + 1) * β k else 0) := by
        rw [mul_add, Finset.mul_sum, Finset.mul_sum]
        simp only [mul_ite, mul_zero]
    _ ≤ (∑ φ, ∑ b, α φ * dAof p φ (s, b)) + ∑ k : KapI ν r1 E, ∑ b, β k * dBof p k (s, b) :=
        add_le_add (Finset.sum_le_sum fun φ _ => hφ φ) (Finset.sum_le_sum fun k _ => hk k)
    _ = ∑ b, ((∑ φ, α φ * dAof p φ (s, b)) + ∑ k, β k * dBof p k (s, b)) := by
        rw [Finset.sum_add_distrib]
        congr 1 <;> exact Finset.sum_comm
    _ ≤ ∑ b, e (s, b) := Finset.sum_le_sum fun b _ => hτ (s, b)
    _ = alN e s := rfl
end Formalism.InvariantFactorPaths.G7.ValuationParity
