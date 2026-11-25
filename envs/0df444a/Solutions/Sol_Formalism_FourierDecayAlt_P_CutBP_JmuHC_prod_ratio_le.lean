-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutBP.JmuHC.prod_ratio_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:07:57.606542+00:00
-- url     : https://prove2.me/submissions/bfc8d850-f100-4c68-a18f-972de0a1ed9b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJmuHC
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutBP_JmuHC_prod_one_add_inv_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP.JmuHC
open Finset
variable {n : ℕ}
namespace Formalism.FourierDecayAlt.P.CutBP.JmuHC
theorem _root_.solution (x : Fin n → ℝ) (hinj : Function.Injective x) (hint : ∀ a b, ∃ m : ℤ, x a - x b = m)
    (s : Fin n) (T : Finset (Fin n)) (hs : s ∉ T) :
    ∏ t ∈ T, |x s + 1 - x t| / |x s - x t| ≤ n := by
  classical
  have hne : ∀ t ∈ T, x s ≠ x t := fun t ht e => hs (hinj e ▸ ht)
  rw [← prod_filter_mul_prod_filter_not T (fun t => x t < x s)]

  have hlow : ∏ t ∈ T.filter (fun t => ¬ x t < x s), |x s + 1 - x t| / |x s - x t| ≤ 1 := by
    apply prod_le_one (fun t _ => by positivity)
    intro t ht
    obtain ⟨ht, hlt⟩ := mem_filter.1 ht
    have hgt : x s < x t := lt_of_le_of_ne (not_lt.1 hlt) (hne t ht)
    obtain ⟨m, hmv⟩ := hint t s
    have hm1 : (1 : ℝ) ≤ x t - x s := by
      rw [hmv]
      have : (0 : ℤ) < m := by exact_mod_cast (hmv ▸ sub_pos.2 hgt)
      exact_mod_cast this
    rw [div_le_one (abs_pos.2 (sub_ne_zero.2 (hne t ht)))]
    rw [abs_of_nonpos (by linarith), abs_of_neg (by linarith)]
    linarith

  set Tp := T.filter (fun t => x t < x s) with hTp
  let dN : Fin n → ℕ := fun t => (⌊x s - x t⌋).toNat
  have hdN : ∀ t ∈ Tp, ((dN t : ℕ) : ℝ) = x s - x t ∧ 1 ≤ x s - x t := by
    intro t ht
    obtain ⟨-, hlt⟩ := mem_filter.1 ht
    obtain ⟨m, hmv⟩ := hint s t
    have hm0 : (0 : ℤ) < m := by exact_mod_cast (hmv ▸ sub_pos.2 hlt)
    refine ⟨?_, ?_⟩
    · simp only [dN, hmv, Int.floor_intCast]
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hm0.le]
    · rw [hmv]; exact_mod_cast hm0
  have hinjOn : Set.InjOn dN Tp := by
    intro t ht t' ht' e
    have h1 := (hdN t ht).1
    have h2 := (hdN t' ht').1
    apply hinj
    have : x s - x t = x s - x t' := by rw [← h1, ← h2, e]
    linarith
  have hup : ∏ t ∈ Tp, |x s + 1 - x t| / |x s - x t| = ∏ d ∈ Tp.image dN, (1 + 1 / (d : ℝ)) := by
    rw [prod_image hinjOn]
    refine prod_congr rfl fun t ht => ?_
    obtain ⟨h1, h2⟩ := hdN t ht
    rw [h1, abs_of_pos (by linarith), abs_of_pos (by linarith)]
    field_simp
    ring
  have hD0 : 0 ∉ Tp.image dN := by
    intro h
    obtain ⟨t, ht, e⟩ := mem_image.1 h
    have h1 := hdN t ht
    rw [e] at h1
    simp at h1
    linarith [h1.1, h1.2]
  have hbound := prod_one_add_inv_le (Tp.image dN) hD0
  rw [card_image_of_injOn hinjOn] at hbound
  have hTcard : Tp.card + 1 ≤ n := by
    have h1 : Tp.card ≤ T.card := card_le_card (filter_subset _ _)
    have h2 : T.card < n := by
      have := card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨subset_univ T, fun e => hs (e ▸ mem_univ s)⟩)
      simpa using this
    omega
  have hupnn : 0 ≤ ∏ t ∈ Tp, |x s + 1 - x t| / |x s - x t| := prod_nonneg fun t _ => by positivity
  calc (∏ t ∈ Tp, |x s + 1 - x t| / |x s - x t|) *
        ∏ t ∈ T.filter (fun t => ¬ x t < x s), |x s + 1 - x t| / |x s - x t|
      ≤ (∏ t ∈ Tp, |x s + 1 - x t| / |x s - x t|) * 1 := mul_le_mul_of_nonneg_left hlow hupnn
    _ ≤ (n : ℝ) := by
        rw [mul_one, hup]
        refine hbound.trans ?_
        exact_mod_cast hTcard
end Formalism.FourierDecayAlt.P.CutBP.JmuHC
