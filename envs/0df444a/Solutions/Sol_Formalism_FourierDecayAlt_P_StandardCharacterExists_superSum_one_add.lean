-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StandardCharacterExists.superSum_one_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:31:23.138328+00:00
-- url     : https://prove2.me/submissions/6518b2f3-f2f2-44cb-970b-203fcf2b75d2

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StandardCharacterExists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StandardCharacterExists
namespace Formalism.FourierDecayAlt.P.StandardCharacterExists
theorem _root_.solution {n : ℕ} (S : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    superSum (1 + S) = superSum S := by
  unfold superSum
  refine Finset.sum_congr rfl fun i _ => ?_
  have : i.castSucc ≠ i.succ := (Fin.castSucc_lt_succ (i := i)).ne
  simp [this]
end Formalism.FourierDecayAlt.P.StandardCharacterExists
