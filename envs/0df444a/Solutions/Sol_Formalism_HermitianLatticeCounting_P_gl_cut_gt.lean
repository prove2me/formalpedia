-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.gl_cut_gt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:45.649264+00:00
-- url     : https://prove2.me/submissions/03a09ab2-cde3-4e88-8794-dddf3b33a224

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment

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
theorem _root_.solution {K L y : ℝ} (hK : 0 ≤ K) (hL : 0 < L) (h : L < y) :
    y * TruncationCutoff K L y = L ^ K * y ^ (1 - K) := by
  have hy : 0 < y := hL.trans h
  unfold TruncationCutoff
  rw [if_neg hy.ne', min_eq_right]
  · rw [Real.div_rpow hL.le hy.le, Real.rpow_sub hy, Real.rpow_one]
    ring
  · exact Real.rpow_le_one (div_nonneg hL.le hy.le) ((div_le_one hy).mpr h.le) hK
end Formalism.HermitianLatticeCounting.P
