-- Prove2me | solution 1 for Formalism.L2.Th1.F.PeriodAreaSignLemmas.det_eq_sgn_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:51:17.77644+00:00
-- url     : https://prove2.me/submissions/125b42d1-f047-46e5-9eca-373b96d42003

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaZeroLogDerivative
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_QuasiPeriodConstUniqueOf
import Theorems.Thm_Formalism_L2_Th1_F_PeriodAreaSignLemmas_det_ne_zero
import Theorems.Thm_Formalism_L2_Th1_F_PeriodAreaSignLemmas_div_im_pos_iff
import Theorems.Thm_Formalism_L2_Th1_F_PeriodAreaSignLemmas_area_eq

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
open Formalism.L2.Th1.F.PeriodAreaSignLemmas
namespace Formalism.L2.Th1.F.PeriodAreaSignLemmas
theorem _root_.solution (L : PeriodPair) : det L = (sgn L : ℝ) * area L := by
  rw [area_eq, sgn]
  split_ifs with h
  · rw [abs_of_pos ((div_im_pos_iff L).mp h)]; simp
  · have : det L < 0 := lt_of_le_of_ne (not_lt.mp (fun h' => h ((div_im_pos_iff L).mpr h')))
      (det_ne_zero L)
    rw [abs_of_neg this]; simp
end Formalism.L2.Th1.F.PeriodAreaSignLemmas
