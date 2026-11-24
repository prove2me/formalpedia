-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx2.PolyFam.at
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:13:41.759278+00:00
-- url     : https://prove2.me/submissions/13e82f72-5bbe-4035-b5fa-230926c81dbf

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
namespace PolyFam
theorem _root_.solution {N : ℕ} {h : ℂ → Mx k r → E} (H : PolyFam k r i D N h) {x : Mx k r}
    (hx : x ∈ Glev k r i ∩ D) : PolyAt N (fun Y => h Y x) := by
  obtain ⟨c, hc, he⟩ := H
  exact ⟨fun j => c j x, fun Y => he Y x hx⟩
end PolyFam
end Formalism.FourierDecayAlt.P.Qx2
