-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.PC.IsPolyS.sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:10:23.653795+00:00
-- url     : https://prove2.me/submissions/0165c146-c6eb-4669-92dd-1cc6a376bc66

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx6 Formalism.FourierDecayAlt.P.Mx6.PC
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W
noncomputable section
variable {B : Type*} [Ring B] [Algebra ℂ B]
namespace Formalism.FourierDecayAlt.P.Mx6.PC
namespace IsPolyS
theorem _root_.solution {a b : ℂ → ℂ} (ha : IsPolyS a) (hb : IsPolyS b) : IsPolyS fun y => a y - b y := by
  obtain ⟨p, hp⟩ := ha; obtain ⟨q, hq⟩ := hb
  exact ⟨p - q, fun y => by show a y - b y = _; rw [hp, hq, eval_sub]⟩
end IsPolyS
end Formalism.FourierDecayAlt.P.Mx6.PC
