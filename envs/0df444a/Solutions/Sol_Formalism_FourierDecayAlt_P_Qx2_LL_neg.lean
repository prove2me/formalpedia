-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx2.LL.neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:15:50.9892+00:00
-- url     : https://prove2.me/submissions/deadb83a-297b-4ebb-b531-b1a6f0db8478

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
namespace LL
theorem _root_.solution {T : (Mx k r → E) → Mx k r → E} (h : LL k r i D T) : LL k r i D (fun f => -(T f)) := by
  refine ⟨fun f f₂ hh x hx => ?_, fun f f₂ s hf hf₂ x hx => ?_⟩
  · simp only [Pi.neg_apply, h.loc f f₂ hh x hx]
  · simp only [Pi.neg_apply, h.lin f f₂ s hf hf₂ x hx, neg_add, smul_neg]
end LL
end Formalism.FourierDecayAlt.P.Qx2
