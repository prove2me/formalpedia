-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TBBx1.admissible_word_nil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:58:40.915219+00:00
-- url     : https://prove2.me/submissions/e8703a40-f330-43f6-a661-4751f763a7a0

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
variable {P : M.Par} {l0 : ℕ} {Y : Finset ℝ} {N : ℕ}
namespace Formalism.FourierDecayAlt.P.TBBx1
theorem _root_.solution : AdmW P l0 Y [] :=
  ⟨⟨fun a => (Nat.not_lt_zero _ a.2).elim, fun a => (Nat.not_lt_zero _ a.2).elim⟩, by simp⟩
end Formalism.FourierDecayAlt.P.TBBx1
