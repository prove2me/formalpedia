-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TBBx1.truncated_exponential_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:58:42.828995+00:00
-- url     : https://prove2.me/submissions/33f06a0e-5af6-4cf1-a21e-5e64c3d423e9

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
theorem _root_.solution (x t : ℝ) (hx : 0 ≤ x) (ht : 0 ≤ t) : 0 ≤ Formalism.HermitianLatticeCounting.ExpansionTerms.TruncationCutoff 3 x t := by
  unfold Formalism.HermitianLatticeCounting.ExpansionTerms.TruncationCutoff
  split_ifs
  · norm_num
  · exact le_min zero_le_one (Real.rpow_nonneg (div_nonneg hx ht) _)
end Formalism.FourierDecayAlt.P.TBBx1
