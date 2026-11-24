-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.gl_e3Integral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:34.902801+00:00
-- url     : https://prove2.me/submissions/ad25d960-ad79-4dee-a19d-a89df3ecefb7

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gl_radial_integrable
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gl_radial_integral
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gl_cut_le
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gl_cut_gt
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_integrableOn_Ioc_truncated_power_moment
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_integrableOn_Ioi_truncated_power_moment

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.ExpansionTerms MeasureTheory Real
open scoped FourierTransform RealInnerProductSpace
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.ExpansionTerms.CutoffIntegralFormula := by
  intro K L hK hL
  have hK0 : 0 ≤ K := by linarith
  have hU : Set.Ioi (0 : ℝ) = Set.Ioc 0 L ∪ Set.Ioi L := (Set.Ioc_union_Ioi_eq_Ioi hL.le).symm
  constructor
  · rw [gl_radial_integrable (fun y => TruncationCutoff K L y), hU]
    exact (integrableOn_Ioc_truncated_power_moment hK0).union (integrableOn_Ioi_truncated_power_moment hK hL)
  · rw [gl_radial_integral (fun y => TruncationCutoff K L y), hU,
      setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi (integrableOn_Ioc_truncated_power_moment hK0)
        (integrableOn_Ioi_truncated_power_moment hK hL),
      setIntegral_congr_fun measurableSet_Ioc (fun y hy => gl_cut_le hK0 hy.1 hy.2),
      setIntegral_congr_fun measurableSet_Ioi (fun y hy => gl_cut_gt hK0 hL hy),
      integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : 1 - K < -1) hL,
      ← intervalIntegral.integral_of_le hL.le, integral_id]
    have e : L ^ K * L ^ (1 - K + 1) = L ^ 2 := by
      rw [← Real.rpow_add hL, ← Real.rpow_natCast]
      congr 1
      push_cast
      ring
    have hK2 : K - 2 ≠ 0 := by linarith [hK]
    have hK3 : 1 - K + 1 ≠ 0 := by
      intro h
      apply hK2
      linarith
    have e2 : L ^ K * (-L ^ (1 - K + 1) / (1 - K + 1)) = L ^ 2 / (K - 2) := by
      rw [← e]
      field_simp
      ring
    rw [e2]
    field_simp
    ring
end Formalism.HermitianLatticeCounting.P
