-- Prove2me | solution 1 for Formalism.L2.Th1.F.Hk2.hk_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:46:08.456825+00:00
-- url     : https://prove2.me/submissions/c06075b7-7ca7-4dfc-89f1-80dd4c010bd6

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HkRowIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HeckeKernelCellContinuous
import Theorems.Thm_Formalism_L2_Th1_F_Hk2_pt_ne_zero
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_mul
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_pow
import Theorems.Thm_Formalism_G_LogCR_Agree_mul


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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Hk2
namespace Formalism.L2.Th1.F.Hk2
theorem _root_.solution {τ : ℂ} (hτ : τ.im ≠ 0) {n : ℤ} (hn : n ≠ 0) (m : ℤ) :
    Continuous (Function.uncurry fun (s x : ℝ) => hk s ((m : ℂ) + (x : ℂ) + (n : ℂ) * τ)) := by
  unfold hk Function.uncurry
  have c : Continuous fun q : ℝ × ℝ => (m : ℂ) + ((q.2 : ℝ) : ℂ) + (n : ℂ) * τ := by fun_prop
  refine Continuous.mul ?_ ?_
  · exact (c.pow 2).inv₀ (fun q => pow_ne_zero 2 (pt_ne_zero hτ hn m q.2))
  · refine Complex.continuous_ofReal.comp ?_
    refine Continuous.rpow c.norm (by fun_prop) (fun q => Or.inl ?_)
    exact norm_ne_zero_iff.mpr (pt_ne_zero hτ hn m q.2)
end Formalism.L2.Th1.F.Hk2
