-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx2.good_rd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:49:35.201844+00:00
-- url     : https://prove2.me/submissions/d3f49b30-b258-48ab-b227-9bb1eb86292a

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_rd_smooth
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_rd_loc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_rd_lin

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
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.P.Qx2
theorem _root_.solution (hD : IsOpen D) {X : Mx k r} (hX : inLieLev k r i X) :
    Good k r i D (fun f : Mx k r → E => RdV X f) := ⟨fun f hf => rd_smooth hf hX, fun f f₂ h x hx => rd_loc hD h hx hX,
    fun f f₂ s hf hf₂ x hx => rd_lin hf hf₂ s hx hX⟩
end Formalism.FourierDecayAlt.P.Qx2
