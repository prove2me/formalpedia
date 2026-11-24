-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.polynomial_sign
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:27:45.045511+00:00
-- url     : https://prove2.me/submissions/9acbcd97-296d-41d5-a60f-e36f14052869

import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RhoAntitoneOfInterlacing
import Theorems.Thm_Formalism_FourierDecayAlt_P_lambda_side_inequality
import Theorems.Thm_Formalism_FourierDecayAlt_P_rho_side_inequality
import Theorems.Thm_Formalism_FourierDecayAlt_P_sign_prod_of_split_at_index

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C7.PSign := by
  unfold C7.PSign
  intro k r u u' ρ lam l Y hl hlk hL hL' hI hB
  have hside := lambda_side_inequality k r u u' lam l Y hl hlk hL hL' hB
  have hrho := rho_side_inequality k u u' ρ l Y hl hlk hI hB
  have hB' := hB
  unfold C7.Between at hB'
  have hA : 0 < (-1 : ℝ) ^ (k - l) * ∏ s, (Y + lam s) := by
    have hprod : ∏ s, (Y + lam s) = ∏ j ∈ Finset.range (k + 2 * r + 1),
        (fun j => if h : j < k + 2 * r + 1 then Y + lam ⟨j, h⟩ else 1) j := by
      rw [← Fin.prod_univ_eq_prod_range]
      refine Finset.prod_congr rfl fun s _ => ?_
      simp only [dif_pos s.isLt, Fin.eta]
    have key := sign_prod_of_split_at_index (Finset.range (k + 2 * r + 1))
      (fun j => if h : j < k + 2 * r + 1 then Y + lam ⟨j, h⟩ else 1) (l - 1)
      (fun j hj hjm => by
        have hj' : j < k + 2 * r + 1 := Finset.mem_range.1 hj
        simp only [dif_pos hj']
        have := (hside ⟨j, hj'⟩).2 (show j + 1 < l by omega)
        linarith [hB'.2])
      (fun j hj hjm => by
        have hj' : j < k + 2 * r + 1 := Finset.mem_range.1 hj
        simp only [dif_pos hj']
        have := (hside ⟨j, hj'⟩).1 (show l ≤ j + 1 by omega)
        linarith [hB'.1])
    have hcard : ((Finset.range (k + 2 * r + 1)).filter (l - 1 ≤ ·)).card = (k - l) + 2 * (r + 1) := by
      rw [(show (Finset.range (k + 2 * r + 1)).filter (l - 1 ≤ ·) = Finset.Ico (l - 1) (k + 2 * r + 1) by
        ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega), Nat.card_Ico]
      omega
    rw [hcard, pow_add, pow_mul, neg_one_sq, one_pow, mul_one] at key
    rw [hprod]
    exact key
  have hB2 : 0 < (-1 : ℝ) ^ (k - l) * I.xpoly k ρ Y := by
    unfold I.xpoly
    have key := sign_prod_of_split_at_index (Finset.Icc 1 (k - 1)) (fun i => Y + ρ i) l
      (fun i hi hil => show 0 < Y + ρ i by linarith [(hrho i hi).2 hil])
      (fun i hi hli => show Y + ρ i < 0 by linarith [(hrho i hi).1 hli])
    have hcard : ((Finset.Icc 1 (k - 1)).filter (l ≤ ·)).card = k - l := by
      rw [(show (Finset.Icc 1 (k - 1)).filter (l ≤ ·) = Finset.Icc l (k - 1) by
        ext j; simp only [Finset.mem_filter, Finset.mem_Icc]; omega), Nat.card_Icc]
      omega
    rw [hcard] at key
    exact key
  refine ⟨hA, hB2, ?_⟩
  have h := abs_of_pos hA
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] at h
  exact h
end Formalism.FourierDecayAlt.P
