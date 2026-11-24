-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx2.PolyAt.smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:15:44.610918+00:00
-- url     : https://prove2.me/submissions/0ac9c098-544d-442e-86f3-b3dccb762978

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
namespace PolyAt
theorem _root_.solution {N : ℕ} {φ : ℂ → E} (H : PolyAt N φ) (s : ℂ) : PolyAt N (fun Y => s • φ Y) := by
  obtain ⟨c, hc⟩ := H
  refine ⟨fun j => s • c j, fun Y => ?_⟩
  try dsimp only
  rw [hc Y, Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _
end PolyAt
end Formalism.FourierDecayAlt.P.Qx2
