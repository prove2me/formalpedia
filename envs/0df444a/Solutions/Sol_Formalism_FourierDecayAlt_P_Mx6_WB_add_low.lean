-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.WB.add_low
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:32:39.671415+00:00
-- url     : https://prove2.me/submissions/ad43cdb1-c93c-4edd-912d-2fada5be5e31

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx6 Formalism.FourierDecayAlt.P.Mx6.WB
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt
noncomputable section
namespace Formalism.FourierDecayAlt.P.Mx6.WB
theorem _root_.solution {p r : ℂ[X]} (hp : p.Monic) (hr : r.natDegree + 1 < p.natDegree) :
    (p + r).Monic ∧ (p + r).natDegree = p.natDegree ∧ (p + r).nextCoeff = p.nextCoeff := by
  have hd : (p + r).natDegree = p.natDegree := natDegree_add_eq_left_of_natDegree_lt (by omega)
  refine ⟨hp.add_of_left (degree_lt_degree (by omega)), hd, ?_⟩
  rw [nextCoeff_of_natDegree_pos (by omega), nextCoeff_of_natDegree_pos (by omega), hd, coeff_add,
    coeff_eq_zero_of_natDegree_lt (p := r) (by omega), add_zero]
end Formalism.FourierDecayAlt.P.Mx6.WB
