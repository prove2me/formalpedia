-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TBBx1.fsv_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:58:40.412833+00:00
-- url     : https://prove2.me/submissions/fcb6d1d3-7a72-4ab7-b76d-5c0b06b7fba7

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MinLeTruncatedExponential

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TBBx1
open Finset Filter Topology MeasureTheory Real
open Formalism.FourierDecayAlt.TBB
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
namespace Formalism.FourierDecayAlt.P.TBBx1
theorem _root_.solution (s c : ℂ) : P5.fsv s c = Complex.exp (2 * Complex.I * ((s * c).im : ℂ)) := by
  unfold P5.fsv
  congr 1
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
end Formalism.FourierDecayAlt.P.TBBx1
