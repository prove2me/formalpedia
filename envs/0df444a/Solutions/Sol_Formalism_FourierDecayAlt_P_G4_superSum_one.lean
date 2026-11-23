-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G4.superSum_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:08.833779+00:00
-- url     : https://prove2.me/submissions/9f24d4a1-4e88-46cf-a4e8-d02ac3b87cdb

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerBlockPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.FourierDecayAlt.G
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G4
namespace Formalism.FourierDecayAlt.P.G4
theorem _root_.solution {n : ℕ} : superSum (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = 0 := by
  unfold superSum
  refine Finset.sum_eq_zero fun i _ => ?_
  exact Matrix.one_apply_ne (Fin.castSucc_lt_succ).ne
end Formalism.FourierDecayAlt.P.G4
