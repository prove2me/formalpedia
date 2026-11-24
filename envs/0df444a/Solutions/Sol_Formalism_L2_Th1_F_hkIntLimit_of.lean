-- Prove2me | solution 1 for Formalism.L2.Th1.F.hkIntLimit_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:04:16.159235+00:00
-- url     : https://prove2.me/submissions/69a35cd8-6f4f-4d07-b9eb-8213242c33d6

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HkRowIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HeckeKernelLineZero
import Theorems.Thm_Formalism_L2_Th1_F_Hk3_term_eq
import Theorems.Thm_Formalism_L2_Th1_F_Hk3_tsum_eq
import Theorems.Thm_Formalism_L2_Th1_F_Hk3_real_limit
import Theorems.Thm_Formalism_ELL_EulerSeries_Agree_mul_right
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Filter MeasureTheory
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
namespace Formalism.L2.Th1.F
theorem _root_.solution (hv : HkIntValue) (hj : HkJRules) : HkIntLimit := by
  intro τ hτ
  refine ⟨fun s hs => ?_, ?_⟩
  · simp_rw [Hk3.term_eq hv hτ hs]
    exact Complex.summable_ofReal.mpr
      ((Real.summable_abs_int_rpow (b := 1 + 2 * s) (by linarith)).mul_right _)
  · have h := (Complex.continuous_ofReal.tendsto _).comp (Hk3.real_limit hj hτ)
    rw [Complex.ofReal_neg] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (Hk3.tsum_eq hv hj hτ hs).symm
end Formalism.L2.Th1.F
