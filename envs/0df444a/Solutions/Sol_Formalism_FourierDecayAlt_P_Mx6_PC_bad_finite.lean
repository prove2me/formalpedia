-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.PC.bad_finite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:32:38.792295+00:00
-- url     : https://prove2.me/submissions/e5447e71-db6d-47d3-9d27-6d9b372a068c

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
variable (P : Par)
namespace Formalism.FourierDecayAlt.P.Mx6.PC
theorem _root_.solution : {Y : ℂ | ¬ Good P Y}.Finite := by
  classical
  refine Set.Finite.subset (Finset.finite_toSet ((Finset.univ : Finset (Ty P)).biUnion fun π =>
    (Icc 1 (P.k - 1)).biUnion fun j => ({-2, -1, 0, 1, 2} : Finset ℤ).image fun n : ℤ => -(rho P π j : ℂ) - (n : ℂ))) ?_
  intro Y hY
  simp only [Set.mem_ofPred_eq, Good, not_forall, not_not] at hY
  obtain ⟨π, j, hj, n, hn, h⟩ := hY
  exact Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨π, Finset.mem_univ _, Finset.mem_biUnion.mpr ⟨j, hj,
    Finset.mem_image.mpr ⟨n, hn, by linear_combination -h⟩⟩⟩)
end Formalism.FourierDecayAlt.P.Mx6.PC
