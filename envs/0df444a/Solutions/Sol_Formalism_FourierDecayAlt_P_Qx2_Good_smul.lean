-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx2.Good.smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:35:03.380019+00:00
-- url     : https://prove2.me/submissions/2be0ceb1-0418-47aa-9c28-4aec05757cc0

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_smooth_smul

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
namespace Good
theorem _root_.solution {T : (Mx k r → E) → Mx k r → E} (hT : Good k r i D T) (c : ℂ) :
    Good k r i D (fun f x => c • T f x) := by
  refine ⟨fun f hf => smooth_smul (hT.sm f hf) c, fun f f₂ h x hx => ?_,
    fun f f₂ s hf hf₂ x hx => ?_⟩
  · try dsimp only
    rw [hT.loc f f₂ h x hx]
  · try dsimp only
    rw [hT.lin f f₂ s hf hf₂ x hx, smul_add, smul_comm c s]
end Good
end Formalism.FourierDecayAlt.P.Qx2
