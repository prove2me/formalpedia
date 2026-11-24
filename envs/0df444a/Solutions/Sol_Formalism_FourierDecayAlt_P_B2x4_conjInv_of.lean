-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x4.conjInv_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:45:31.616286+00:00
-- url     : https://prove2.me/submissions/c543acdd-e53e-4d4c-a1e1-4c68498d6117

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Theorems.Thm_Formalism_FourierDecayAlt_P_conjugation_invariance_of_parts
import Theorems.Thm_Formalism_FourierDecayAlt_P_compact_subgroup_conjugation
import Theorems.Thm_Formalism_QuantumDeterminants_uWNormal


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
namespace B2x4
theorem _root_.solution (hN : ClosedN) (hW : ClosedW) (hK : CompactW) : ConjInvRaw ∧ ConjInvAll :=
  conjugation_invariance_of_parts compact_subgroup_conjugation hN hW hK uWNormal
end B2x4
end Formalism.FourierDecayAlt.P
