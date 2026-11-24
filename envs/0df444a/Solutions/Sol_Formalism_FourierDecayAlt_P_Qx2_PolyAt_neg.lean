-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx2.PolyAt.neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:28:26.364132+00:00
-- url     : https://prove2.me/submissions/c1c9f35f-361b-4bd1-a7c4-0e58442865e2

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
theorem _root_.solution {N : ℕ} {φ : ℂ → E} (H : PolyAt N φ) : PolyAt N (fun Y => -φ Y) := by
  obtain ⟨c, hc⟩ := H
  refine ⟨fun j => -c j, fun Y => ?_⟩
  try dsimp only
  rw [hc Y]
  simp [smul_neg, Finset.sum_neg_distrib]
end PolyAt
end Formalism.FourierDecayAlt.P.Qx2
