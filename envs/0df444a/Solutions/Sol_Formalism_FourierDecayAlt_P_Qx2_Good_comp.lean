-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx2.Good.comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:13:50.547011+00:00
-- url     : https://prove2.me/submissions/70af9c30-8d2b-4ae3-a1dc-523d463edc36

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta

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
theorem _root_.solution {T S : (Mx k r → E) → Mx k r → E} (hT : Good k r i D T) (hS : Good k r i D S) :
    Good k r i D (fun f => T (S f)) := by
  refine ⟨fun f hf => hT.sm _ (hS.sm f hf), fun f f₂ h x hx => hT.loc _ _ (hS.loc f f₂ h) x hx,
    fun f f₂ s hf hf₂ x hx => ?_⟩
  exact (hT.loc _ _ (fun y hy => hS.lin f f₂ s hf hf₂ y hy) x hx).trans
    (hT.lin _ _ s (hS.sm f hf) (hS.sm f₂ hf₂) x hx)
end Good
end Formalism.FourierDecayAlt.P.Qx2
