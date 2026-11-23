-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.gl_cut_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:46.470848+00:00
-- url     : https://prove2.me/submissions/500726c7-3ae9-4fed-adae-b61a9af51fba

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
theorem _root_.solution {K L y : ℝ} (hK : 0 ≤ K) (hy : 0 < y) (h : y ≤ L) : y * TruncationCutoff K L y = y := by
  unfold TruncationCutoff
  rw [if_neg hy.ne', min_eq_left, mul_one]
  exact Real.one_le_rpow ((one_le_div hy).mpr h) hK
end Formalism.HermitianLatticeCounting.P
