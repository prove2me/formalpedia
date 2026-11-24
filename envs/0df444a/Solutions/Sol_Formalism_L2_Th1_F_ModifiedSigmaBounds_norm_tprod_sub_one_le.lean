-- Prove2me | solution 1 for Formalism.L2.Th1.F.ModifiedSigmaBounds.norm_tprod_sub_one_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:52:55.037429+00:00
-- url     : https://prove2.me/submissions/b71c31fe-216a-459d-873d-d1bb80781ca7

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaZeroLogDerivative
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaConv
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SgStar
import Theorems.Thm_Formalism_L2_Th1_F_SigmaConv_norm_wFactor_sub_one_le
import Theorems.Thm_Formalism_L2_Th1_F_SigmaConv_summable_majorant


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Filter
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open ModifiedSigmaBounds
open Formalism.L2.Th1.F.ModifiedSigmaBounds
open SigmaConv
namespace Formalism.L2.Th1.F.ModifiedSigmaBounds
theorem _root_.solution (hs : SigmaSummable) (L : PeriodPair) (z : ℂ)
    (hz : ∀ l : L.lattice, (l : ℂ) ≠ 0 → 2 * ‖z‖ ≤ ‖(l : ℂ)‖) :
    ‖∏' l : L.lattice, wFactor (l : ℂ) z - 1‖
      ≤ Real.exp (∑' l : L.lattice, 2 * ‖z‖ ^ 3 * ‖l‖ ^ (-3 : ℝ)) - 1 := by
  have hm : Multipliable (fun l : L.lattice => 1 + (wFactor (l : ℂ) z - 1)) :=
    multipliable_one_add_of_summable (hs L z)
  have ht : Tendsto (fun t : Finset L.lattice => ‖∏ l ∈ t, (1 + (wFactor (l : ℂ) z - 1)) - 1‖)
      atTop (nhds ‖∏' l : L.lattice, (1 + (wFactor (l : ℂ) z - 1)) - 1‖) :=
    (Tendsto.sub_const hm.hasProd 1).norm
  simp only [add_sub_cancel] at ht
  refine le_of_tendsto ht (Eventually.of_forall fun t => ?_)
  have h1 := t.norm_prod_one_add_sub_one_le (fun l : L.lattice => wFactor (l : ℂ) z - 1)
  simp only [add_sub_cancel] at h1
  refine h1.trans ?_
  have h2 : ∑ l ∈ t, ‖wFactor (l : ℂ) z - 1‖ ≤ ∑' l : L.lattice, 2 * ‖z‖ ^ 3 * ‖l‖ ^ (-3 : ℝ) := by
    refine (Finset.sum_le_sum fun l _ => ?_).trans
      ((summable_majorant L ‖z‖).sum_le_tsum t fun l _ => by positivity)
    by_cases hl : (l : ℂ) = 0
    · simp only [hl, wFactor, div_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, mul_zero, add_zero, Complex.exp_zero, mul_one, sub_self, norm_zero]
      positivity
    · exact norm_wFactor_sub_one_le ‖z‖ l z le_rfl (hz l hl)
  have := Real.exp_le_exp.mpr h2
  linarith
end Formalism.L2.Th1.F.ModifiedSigmaBounds
