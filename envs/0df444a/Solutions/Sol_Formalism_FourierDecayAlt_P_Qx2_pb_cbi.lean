-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx2.pb_cbi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:06:30.264428+00:00
-- url     : https://prove2.me/submissions/7dbc5210-82ea-4c73-bda3-41e7c0f021f4

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_cbiOp_add
import Theorems.Thm_Formalism_QuantumDeterminants_presOps
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
open Formalism.FourierDecayAlt.P.Qx2
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ}
namespace Formalism.FourierDecayAlt.P.Qx2
theorem _root_.solution (l : Fin m) {f : (Fin m → ℂ) → E} (hf : f ∈ WSm m E) :
    pbOp l (cbiOp l f) = cbiOp l (pbOp l f) - cbiOp l f := by
  have h1 : cbiOp l f ∈ WSm m E := presOps m E l 5 f hf
  have h2 : pbOp l (cbiOp l f) ∈ WSm m E := presOps m E l 3 _ h1
  obtain ⟨-, -, -, hA, -, -⟩ := weylFun m E l f hf
  obtain ⟨-, -, -, -, -, hC⟩ := weylFun m E l _ h1
  obtain ⟨-, -, -, -, hB, -⟩ := weylFun m E l _ h2
  rw [hA] at hC
  rw [hC, cbiOp_add, hB]
  abel
end Formalism.FourierDecayAlt.P.Qx2
