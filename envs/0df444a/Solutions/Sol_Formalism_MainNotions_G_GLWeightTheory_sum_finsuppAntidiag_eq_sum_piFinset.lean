-- Prove2me | solution 1 for Formalism.MainNotions.G.GLWeightTheory.sum_finsuppAntidiag_eq_sum_piFinset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:40:10.25821+00:00
-- url     : https://prove2.me/submissions/cd2a9480-5498-4be8-8384-873f6ebace5f

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_MatrixSubstTransvectionMonomialOfFixed
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_SumFinsuppAntidiagEqSumPiFinset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory
open Formalism.MainNotions.G
variable {B : Type*} [CommRing B] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
  (a b : Fin n) (t : B) (m : ι × Fin n →₀ ℕ)
open Classical
namespace Formalism.MainNotions.G.GLWeightTheory
theorem _root_.solution (k : ℕ) :
    ∑ f ∈ Finset.finsuppAntidiag (Finset.univ.filter (· ∈ S)) k,
      monomial (shiftedExponent LL a b m (⇑f)) (rootShiftCoefficient B LL a b m (⇑f)) =
    ∑ p ∈ (Fintype.piFinset (fun l : ι => Finset.range (sourceExp LL S a b m l + 1))).filter (fun p => ∑ l, p l = k),
      monomial (shiftedExponent LL a b m p) (rootShiftCoefficient B LL a b m p) := by
  have hcf : ∀ p : ι → ℕ, rootShiftCoefficient B LL a b m p ≠ 0 → ∀ l, p l ≤ m (sourceVar LL a b l) := by
    intro p hp l
    by_contra hlt
    push_neg at hlt
    apply hp
    unfold rootShiftCoefficient
    refine Finset.prod_eq_zero (Finset.mem_univ l) ?_
    unfold sourceVar at hlt
    split_ifs at hlt ⊢ with hv
    · rw [Nat.choose_eq_zero_of_lt hlt, Nat.cast_zero]
    · rw [Nat.choose_eq_zero_of_lt hlt, Nat.cast_zero, mul_zero]
  have hmon : ∀ (s : ι × Fin n →₀ ℕ) (c : B),
      (monomial s c : MvPolynomial (ι × Fin n) B) ≠ 0 → c ≠ 0 :=
    fun s c h hc => h (by rw [hc, map_zero])
  have hsumS : ∀ p : ι → ℕ, (∀ l, l ∉ S → p l = 0) →
      ∑ l ∈ Finset.univ.filter (· ∈ S), p l = ∑ l, p l := by
    intro p hp
    refine Finset.sum_subset (Finset.subset_univ _) fun l _ hl => hp l ?_
    intro hS
    exact hl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS⟩)
  refine Finset.sum_bij_ne_zero (fun f _ _ => ⇑f) ?_ ?_ ?_ ?_
  · intro f hf hne
    rw [Finset.mem_finsuppAntidiag] at hf
    have hz : ∀ l, l ∉ S → f l = 0 := fun l hl => by
      by_contra h
      exact hl (Finset.mem_filter.mp (hf.2 (Finsupp.mem_support_iff.mpr h))).2
    simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
    refine ⟨fun l => ?_, ?_⟩
    · rw [Nat.lt_succ_iff]
      by_cases hl : l ∈ S
      · rw [sourceExp, if_pos hl]
        exact hcf _ (hmon _ _ hne) l
      · rw [hz l hl]
        exact Nat.zero_le _
    · rw [← hsumS _ hz]
      exact hf.1
  · intro f₁ _ _ f₂ _ _ h
    exact DFunLike.coe_injective h
  · intro p hp hne
    simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hp
    have hle : ∀ l, p l ≤ sourceExp LL S a b m l := fun l => Nat.lt_succ_iff.mp (hp.1 l)
    have hz : ∀ l, l ∉ S → p l = 0 := fun l hl => by
      have h := hle l
      rw [sourceExp, if_neg hl] at h
      omega
    refine ⟨Finsupp.equivFunOnFinite.symm p, ?_, ?_, ?_⟩
    · rw [Finset.mem_finsuppAntidiag, Finsupp.coe_equivFunOnFinite_symm]
      refine ⟨by rw [hsumS _ hz]; exact hp.2, fun l hl => ?_⟩
      rw [Finsupp.mem_support_iff, Finsupp.coe_equivFunOnFinite_symm] at hl
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      by_contra hS
      exact hl (hz l hS)
    · simp only [Finsupp.coe_equivFunOnFinite_symm]
      exact hne
    · exact Finsupp.coe_equivFunOnFinite_symm p
  · intro f _ _
    rfl
end Formalism.MainNotions.G.GLWeightTheory
