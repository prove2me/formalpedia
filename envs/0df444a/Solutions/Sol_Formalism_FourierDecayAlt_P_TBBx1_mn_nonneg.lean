-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TBBx1.mn_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:22:15.820666+00:00
-- url     : https://prove2.me/submissions/e1974900-7506-40a5-8edf-52b5e8934cb1

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
theorem _root_.solution {Λ : ℝ} (hΛ : 0 ≤ Λ) (K : ℕ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ mn Λ K x := by
  unfold mn
  split_ifs
  · norm_num
  · exact le_min zero_le_one (pow_nonneg (div_nonneg hΛ hx) _)
end Formalism.FourierDecayAlt.P.TBBx1
