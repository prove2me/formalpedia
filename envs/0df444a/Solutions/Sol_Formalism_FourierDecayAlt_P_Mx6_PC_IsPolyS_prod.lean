-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.PC.IsPolyS.prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:10:14.504848+00:00
-- url     : https://prove2.me/submissions/5341d5ed-3986-49fe-a955-2b8c910594d9

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
theorem _root_.solution {ι : Type*} (s : Finset ι) {a : ι → ℂ → ℂ} (ha : ∀ i ∈ s, IsPolyS (a i)) :
    IsPolyS fun y => ∏ i ∈ s, a i y := by
  classical
  choose! p hp using ha
  exact ⟨∏ i ∈ s, p i, fun y => by show ∏ i ∈ s, a i y = _; rw [eval_prod]; exact Finset.prod_congr rfl fun i hi => hp i hi y⟩
end IsPolyS
end Formalism.FourierDecayAlt.P.Mx6.PC
