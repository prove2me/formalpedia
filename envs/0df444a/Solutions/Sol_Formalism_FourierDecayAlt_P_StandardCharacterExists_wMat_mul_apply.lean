-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StandardCharacterExists.wMat_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:35:22.402006+00:00
-- url     : https://prove2.me/submissions/5428c6fc-688b-4ae2-9a60-73266e7001c0

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
theorem _root_.solution {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    (wMat d * M) i j = M i.rev j := by
  simp [Matrix.mul_apply, wMat]
end Formalism.FourierDecayAlt.P.StandardCharacterExists
