-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.gl_cut_scale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:53.723728+00:00
-- url     : https://prove2.me/submissions/55fc5f31-3a59-4622-ab19-063eb85c7e4d

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
theorem _root_.solution (x t : ℝ) : TruncationCutoff 3 x (π * t) = TruncationCutoff 3 (x / π) t := by
  unfold TruncationCutoff
  by_cases ht : t = 0
  · simp [ht]
  · have hpt : π * t ≠ 0 := mul_ne_zero Real.pi_ne_zero ht
    rw [if_neg hpt, if_neg ht, div_mul_eq_div_div]
end Formalism.HermitianLatticeCounting.P
