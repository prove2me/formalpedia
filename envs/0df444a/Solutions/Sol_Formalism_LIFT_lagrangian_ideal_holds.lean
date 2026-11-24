-- Prove2me | solution 1 for Formalism.LIFT.lagrangian_ideal_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:46:57.296452+00:00
-- url     : https://prove2.me/submissions/83ffc058-c4b1-4d28-959d-abb070950523

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_LagrangeIdeal
import Theorems.Thm_Formalism_LIFT_prod_X_sub_C_dvd_of_injOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LIFT
open Polynomial
namespace Formalism.LIFT
theorem _root_.solution : LagrangeIdeal := by
  intro R _ _ ℓ ι _ S₁ S₂ c w hdisj hw
  set N := S₁.sup fun a => (∑ b ∈ S₂, w a b) + ∑ a' ∈ S₁.erase a, w a a' with hN
  by_cases hℓN : ℓ ^ N = 0
  · rw [hℓN, map_zero]
    exact Ideal.zero_mem _
  have hleN : ∀ a ∈ S₁, (∑ a' ∈ S₁.erase a, w a a') + ∑ b ∈ S₂, w a b ≤ N := by
    intro a ha
    rw [add_comm]
    exact Finset.le_sup (f := fun a => (∑ b ∈ S₂, w a b) + ∑ a' ∈ S₁.erase a, w a a') ha
  have hval : ∀ a ∈ S₁, ∃ u : R,
      ℓ ^ N = ((∏ a' ∈ S₁.erase a, (c a - c a')) * ∏ b ∈ S₂, (c a - c b)) * u := by
    intro a ha
    have hassoc : Associated ((∏ a' ∈ S₁.erase a, (c a - c a')) * ∏ b ∈ S₂, (c a - c b))
        (ℓ ^ ((∑ a' ∈ S₁.erase a, w a a') + ∑ b ∈ S₂, w a b)) := by
      rw [pow_add, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum]
      refine Associated.mul_mul (Associated.prod _ _ _ fun a' ha' => ?_) (Associated.prod _ _ _ fun b hb => ?_)
      · exact hw a ha a' (Finset.mem_union_left _ (Finset.mem_of_mem_erase ha'))
          (Finset.ne_of_mem_erase ha').symm
      · refine hw a ha b (Finset.mem_union_right _ hb) ?_
        intro hab
        subst hab
        exact Finset.disjoint_left.mp hdisj ha hb
    exact (hassoc.dvd_iff_dvd_left).mpr (pow_dvd_pow ℓ (hleN a ha))
  choose! u hu using hval
  have hinj : Set.InjOn c S₁ := by
    intro a ha a' ha' heq
    by_contra hne
    have hw' : w a a' ≤ N := le_trans (Finset.single_le_sum (f := fun x => w a x)
      (fun _ _ => Nat.zero_le _) (Finset.mem_erase.mpr ⟨Ne.symm hne, ha'⟩)) (le_trans (Nat.le_add_right _ _) (hleN a ha))
    have hpow : ℓ ^ w a a' ≠ 0 := by
      intro h0
      apply hℓN
      rw [← Nat.add_sub_cancel' hw', pow_add, h0, zero_mul]
    have := (hw a ha a' (Finset.mem_union_left _ ha') hne).ne_zero_iff.mpr hpow
    exact this (by rw [heq, sub_self])
  set F : R[X] := ∑ a ∈ S₁, C (u a) * ∏ a' ∈ S₁.erase a, (X - C (c a')) with hF
  have hQ : (∏ a ∈ S₁, (X - C (c a))) ∣ F * ∏ b ∈ S₂, (X - C (c b)) - C (ℓ ^ N) := by
    apply prod_X_sub_C_dvd_of_injOn S₁ c hinj
    intro a ha
    rw [eval_sub, eval_mul, eval_C, hF, eval_finset_sum, Finset.sum_eq_single a]
    · simp only [eval_mul, eval_C, eval_prod, eval_sub, eval_X]
      rw [hu a ha]
      ring
    · intro a₀ _ hne
      rw [eval_mul, eval_prod, Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hne, ha⟩)
        (by simp), mul_zero]
    · intro h
      exact absurd ha h
  obtain ⟨k, hk⟩ := hQ
  have hC : C (ℓ ^ N) = F * ∏ b ∈ S₂, (X - C (c b)) - (∏ a ∈ S₁, (X - C (c a))) * k := by
    rw [← hk]
    ring
  rw [hC]
  refine Ideal.sub_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span ?_))
    (Ideal.mul_mem_right _ _ (Ideal.subset_span ?_))
  · simp
  · simp
end Formalism.LIFT
