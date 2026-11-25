-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.transfer_triples
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:36:20.133874+00:00
-- url     : https://prove2.me/submissions/fe6e32cb-a156-4874-be72-12e441074b9e

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_pbOp_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_cbiOp_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_pb_cbi
import Theorems.Thm_Formalism_QuantumDeterminants_commFun
import Theorems.Thm_Formalism_QuantumDeterminants_weylFun


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Q.TTriples := by
  intro E _ _ m l f hf
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := weylFun m E l f hf
  refine ⟨⟨h1, h2, h3⟩, ⟨h5, h4, ?_⟩, ?_⟩
  · rw [Qx2.pbOp_neg, Qx2.cbiOp_neg, neg_neg, neg_neg, Qx2.pb_cbi l hf, sub_eq_add_neg]
  · intro i j hij
    exact commFun m E l l i j f hf (Or.inr hij)
end Formalism.FourierDecayAlt.P
