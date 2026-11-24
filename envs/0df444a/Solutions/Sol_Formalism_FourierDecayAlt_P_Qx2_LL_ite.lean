-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx2.LL.ite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:15:50.549059+00:00
-- url     : https://prove2.me/submissions/a49586df-7376-46aa-8d93-0e4b1ab99930

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
theorem _root_.solution {T : (Mx k r → E) → Mx k r → E} (h : LL k r i D T) (p : Prop) [Decidable p] :
    LL k r i D (fun f x => if p then T f x else 0) := by
  refine ⟨fun f f₂ hh x hx => ?_, fun f f₂ s hf hf₂ x hx => ?_⟩
  · by_cases hp : p <;> simp [hp, h.loc f f₂ hh x hx]
  · by_cases hp : p <;> simp [hp, h.lin f f₂ s hf hf₂ x hx]
end LL
end Formalism.FourierDecayAlt.P.Qx2
