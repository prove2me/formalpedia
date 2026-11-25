-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.sum_ldeg_div_add_le_sl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:14:11.957745+00:00
-- url     : https://prove2.me/submissions/802eb09b-0792-47ec-98a3-b5b1859446e0

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SumOnLetterApplyInl
import Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_TwistData_hypH__461b564647c2
import Theorems.Thm_Formalism_MainNotions_PlaneGram_divE_apply
import Theorems.Thm_Formalism_MainNotions_PlaneGram_letE_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.PlaneGram.divE_apply
attribute [local simp] Formalism.MainNotions.PlaneGram.letE_apply



set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K]
open Formalism.MainNotions.PlaneGram.TwistData
variable [CharZero K] (D : TwistData K) (v : AddValuation K (WithTop ℚ)) (p : ℕ)
variable {D v p}
variable (D p)
variable {D p}
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (D : TwistData K) (p : ℕ) (hp : 0 < p) (hr : 0 < D.r) (hH : D.HypH p 13) (M : D.EA)
    (hMd : ∀ t : D.Tau, ldeg M (Sum.inr t) ≤ D.dLL t.1) (j : Fin D.J) (i : Fin (D.nch j)) :
    (∑ t : D.Tau, (if t.1 = D.aux₃ j then (ldeg M (Sum.inr t) : ℝ) / (D.P p t : ℝ) + D.c else 0)) +
      12 * D.c ≤ D.sl j i := by
  classical
  have hr' : (0 : ℝ) < D.r := by exact_mod_cast hr
  have hr1 : (1 : ℝ) ≤ D.r := by exact_mod_cast hr
  have hc0 : (0 : ℝ) ≤ D.c := Nat.cast_nonneg _
  have e1 : (∑ t : D.Tau, (if t.1 = D.aux₃ j then (ldeg M (Sum.inr t) : ℝ) / (D.P p t : ℝ) + D.c else 0)) =
      ∑ m : Fin D.r, ((ldeg M (Sum.inr (D.aux₃ j, m)) : ℝ) / (D.P p (D.aux₃ j, m) : ℝ) + D.c) := by
    rw [Fintype.sum_prod_type, Finset.sum_eq_single (D.aux₃ j)]
    · simp
    · intro j0 _ hj0
      simp [hj0]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [e1]
  have e2 : ∀ m : Fin D.r, (ldeg M (Sum.inr (D.aux₃ j, m)) : ℝ) / (D.P p (D.aux₃ j, m) : ℝ) + D.c ≤
      (D.sl j i - 13 * D.r * D.c) / D.r + D.c := by
    intro m
    have hP : (0 : ℝ) < (D.P p (D.aux₃ j, m) : ℝ) := by
      have : 0 < D.P p (D.aux₃ j, m) := pow_pos hp _
      exact_mod_cast this
    have h1 := D.hypH' p 13 hH j m i
    have h2 : (ldeg M (Sum.inr (D.aux₃ j, m)) : ℝ) ≤ D.dLL (D.aux₃ j) := by exact_mod_cast hMd (D.aux₃ j, m)
    have h3 : (ldeg M (Sum.inr (D.aux₃ j, m)) : ℝ) / (D.P p (D.aux₃ j, m) : ℝ) ≤
        (D.dLL (D.aux₃ j) : ℝ) / (D.P p (D.aux₃ j, m) : ℝ) := div_le_div_of_nonneg_right h2 hP.le
    have h4 : (D.dLL (D.aux₃ j) : ℝ) / (D.P p (D.aux₃ j, m) : ℝ) ≤ (D.sl j i - 13 * D.r * D.c) / D.r := by
      rw [le_div_iff₀ hr']
      rw [mul_div_assoc] at h1
      linarith
    linarith
  have e3 := Finset.sum_le_sum (fun m (_ : m ∈ (Finset.univ : Finset (Fin D.r))) => e2 m)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_add,
    mul_div_cancel₀ _ hr'.ne'] at e3
  nlinarith
end Formalism.MainNotions.PlaneGram.TwistData
