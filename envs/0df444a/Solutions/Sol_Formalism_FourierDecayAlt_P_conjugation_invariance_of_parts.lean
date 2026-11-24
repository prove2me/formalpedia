-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.conjugation_invariance_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:43:58.432633+00:00
-- url     : https://prove2.me/submissions/ef6969e0-9db0-429f-81fd-b466d3f59e79

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.B2.AssembleConjInv := by
  intro hCC hN hW hK hU
  have raw : ConjInvRaw := by
    intro k r z μN hz hT hμ h hh
    exact hCC k r (Nset k r) (UWset k r z) μN (hN k r) (hW k r z) (hK k r z hz hT)
      (fun a ha u hu => (hU k r z hz a ha u hu).1) hμ h hh
  refine ⟨raw, ?_⟩
  intro k r Wp Wq _ _ _ _ D h₀ hh
  rcases hh with hh | hh
  · exact raw k r D.z D.μN D.z_mem D.T_pos D.haarN h₀ hh
  · exact raw k r D.z' D.μN D.z'_mem D.T'_pos D.haarN h₀ hh
end Formalism.FourierDecayAlt.P
