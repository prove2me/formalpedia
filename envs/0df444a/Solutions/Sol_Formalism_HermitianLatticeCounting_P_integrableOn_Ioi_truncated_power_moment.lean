-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.integrableOn_Ioi_truncated_power_moment
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:48.582514+00:00
-- url     : https://prove2.me/submissions/d8d88ac4-a504-4b6e-8aa1-308a52423e2f

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gl_cut_gt

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
theorem _root_.solution {K L : ℝ} (hK : 2 < K) (hL : 0 < L) :
    IntegrableOn (fun y : ℝ => y * TruncationCutoff K L y) (Set.Ioi L) := by
  have hE : Set.EqOn (fun y : ℝ => y * TruncationCutoff K L y) (fun y => L ^ K * y ^ (1 - K)) (Set.Ioi L) :=
    fun y hy => gl_cut_gt (by linarith) hL hy
  refine IntegrableOn.congr_fun ?_ hE.symm measurableSet_Ioi
  exact Integrable.const_mul (integrableOn_Ioi_rpow_of_lt (by linarith) hL) _
end Formalism.HermitianLatticeCounting.P
