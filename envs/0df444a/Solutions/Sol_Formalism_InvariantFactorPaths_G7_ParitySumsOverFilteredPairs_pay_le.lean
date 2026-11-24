-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.ParitySumsOverFilteredPairs.pay_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:40.69762+00:00
-- url     : https://prove2.me/submissions/d8346f5d-6b18-4e0f-ba34-8ff3f1a2c8b3

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_GrowthSums_StatementG
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EntryATwoAndB
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ParitySumsOverFilteredPairs_one_le_dAof_left
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ParitySumsOverFilteredPairs_one_le_dAof_right

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
open Formalism.InvariantFactorPaths.G7.ParitySumsOverFilteredPairs
variable {ν r0 r1 E : ℕ}
namespace Formalism.InvariantFactorPaths.G7.ParitySumsOverFilteredPairs
theorem _root_.solution [NeZero ν] {p : ℕ} (hp : 0 < p) (α : PhiI ν r0 r1 E → ℕ) (β : KapI ν r1 E →₀ ℕ)
    (e : TpV ν r1 → ℕ)
    (h3 : ∀ τ, ∑ φ, α φ * dAof p φ τ + ∑ k, β k * dBof p k τ ≤ e τ) (P : Finset (TpV ν r1))
    (hP : ∀ φ, α φ ≠ 0 → (pairFirst φ, φ.2.2.2.2) ∈ P ∨ (pairSecond φ, φ.2.2.2.2) ∈ P) :
    ∑ φ, α φ + ∑ k ∈ univ.filter (fun k : KapI ν r1 E => (k.1, k.2.2) ∈ P), β k ≤
      ∑ τ ∈ P, e τ := by
  have hsum := Finset.sum_le_sum (fun τ (_ : τ ∈ P) => h3 τ)
  have e1 : ∑ τ ∈ P, ∑ φ, α φ * dAof p φ τ = ∑ φ, ∑ τ ∈ P, α φ * dAof p φ τ := Finset.sum_comm
  have e2 : ∑ τ ∈ P, ∑ k, β k * dBof p k τ = ∑ k, ∑ τ ∈ P, β k * dBof p k τ := Finset.sum_comm
  rw [Finset.sum_add_distrib, e1, e2] at hsum
  refine le_trans (add_le_add ?_ ?_) hsum
  · refine Finset.sum_le_sum (fun φ _ => ?_)
    rw [← Finset.mul_sum]
    by_cases hα : α φ = 0
    · simp [hα]
    · have h1 : 1 ≤ ∑ τ ∈ P, dAof p φ τ := by
        rcases hP φ hα with h | h
        · exact le_trans (one_le_dAof_left hp φ) (Finset.single_le_sum (fun _ _ => Nat.zero_le _) h)
        · exact le_trans (one_le_dAof_right hp φ) (Finset.single_le_sum (fun _ _ => Nat.zero_le _) h)
      calc α φ = α φ * 1 := (mul_one _).symm
        _ ≤ α φ * ∑ τ ∈ P, dAof p φ τ := Nat.mul_le_mul_left _ h1
  · rw [Finset.sum_filter]
    refine Finset.sum_le_sum (fun k _ => ?_)
    split_ifs with hk
    · rw [← Finset.mul_sum]
      have h1 : 1 ≤ ∑ τ ∈ P, dBof p k τ := by
        refine le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hk)
        simp only [dBof, Finsupp.single_eq_same]
        exact Nat.one_le_pow _ _ hp
      calc β k = β k * 1 := (mul_one _).symm
        _ ≤ β k * ∑ τ ∈ P, dBof p k τ := Nat.mul_le_mul_left _ h1
    · exact Nat.zero_le _
end Formalism.InvariantFactorPaths.G7.ParitySumsOverFilteredPairs
