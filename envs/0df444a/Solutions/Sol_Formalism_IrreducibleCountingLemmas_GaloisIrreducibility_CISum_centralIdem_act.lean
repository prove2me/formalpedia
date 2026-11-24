-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.CISum.centralIdem_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:51:01.812644+00:00
-- url     : https://prove2.me/submissions/14083590-4b5e-412c-84de-1f4e5e8df007

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_EigenbasisOfDistinctRoots
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCentralIdempotent
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CentralIdempotentsSumOne
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_isIrreducible_of
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_schur_scalar


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
open Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.CISum
open Classical
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.CISum
theorem _root_.solution {G V W : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (hρ : IsIrr ρ) (hσ : IsIrr σ) :
    σ.asAlgebraHom (centralIdem ρ) = if Nonempty (Representation.Equiv ρ σ) then 1 else 0 := by
  have := hρ.1
  have := hσ.1
  have hirrρ : ρ.IsIrreducible := isIrreducible_of ρ hρ.2
  have hirrσ : σ.IsIrreducible := isIrreducible_of σ hσ.2
  have hc0 : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (by rw [Nat.card_eq_fintype_card]; exact hc0)
  set c : ℂ := (Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ) with hc
  have e : σ.asAlgebraHom (centralIdem ρ) = ∑ g, (c * ρ.character g⁻¹) • σ g := by
    unfold centralIdem
    simp [map_sum]
    rfl
  obtain ⟨μ, hμ⟩ := schur_scalar σ hσ.2 (fun g => c * ρ.character g⁻¹) (by
    intro g k
    have : (k * g * k⁻¹)⁻¹ = k * g⁻¹ * k⁻¹ := by group
    simp only [this, Representation.char_conj])
  have htr : μ * (Module.finrank ℂ W : ℂ) = c * ∑ g, σ.character g * ρ.character g⁻¹ := by
    have h1 := congrArg (LinearMap.trace ℂ W) hμ
    simp only [map_sum, map_smul, smul_eq_mul, LinearMap.trace_one] at h1
    rw [← h1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun g _ => by simp only [Representation.character]; ring
  have horth := Representation.char_orthonormal σ ρ
  rw [Nat.card_eq_fintype_card] at horth
  have hd : (Module.finrank ℂ W : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := W)).ne'
  rw [e, hμ]
  split_ifs with hiso
  · rw [if_pos hiso] at horth
    obtain ⟨φ⟩ := hiso
    have hdim : Module.finrank ℂ V = Module.finrank ℂ W := φ.toLinearEquiv.finrank_eq
    have hsum : ∑ g, σ.character g * ρ.character g⁻¹ = (Fintype.card G : ℂ) := by
      field_simp at horth
      simpa using horth
    rw [hsum, hc, hdim, div_mul_cancel₀ _ hc0] at htr
    have : μ = 1 := by
      have := mul_right_cancel₀ hd (htr.trans (one_mul _).symm)
      exact this
    rw [this, one_smul]
  · rw [if_neg hiso] at horth
    have hsum : ∑ g, σ.character g * ρ.character g⁻¹ = 0 := by
      simpa [hc0] using horth
    rw [hsum, mul_zero] at htr
    rw [(mul_eq_zero.mp htr).resolve_right hd, zero_smul]
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.CISum
