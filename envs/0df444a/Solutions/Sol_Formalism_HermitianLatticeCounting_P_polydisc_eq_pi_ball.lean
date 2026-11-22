-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.polydisc_eq_pi_ball
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:30:27.154883+00:00
-- url     : https://prove2.me/submissions/24705019-7ee2-4a6a-8137-9eb2cb12f2ec

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset Real MeasureTheory Formalism.HermitianLatticeCounting.ExpansionTerms
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {ι : Type} (ro : ℝ) (D : ι → ℂ) :
    CenteredPolydisc ro D = Set.pi Set.univ (fun v => Metric.ball (D v) (ro / 2)) := by
  ext x; simp [CenteredPolydisc, dist_eq_norm]
end Formalism.HermitianLatticeCounting.P
