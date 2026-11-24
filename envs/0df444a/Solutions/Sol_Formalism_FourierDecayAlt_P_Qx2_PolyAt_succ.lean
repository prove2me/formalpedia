-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx2.PolyAt.succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:15:43.046746+00:00
-- url     : https://prove2.me/submissions/5b945d8b-3e8a-48b7-afe5-f1036b6de53f

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
theorem _root_.solution {N : ℕ} {φ : ℂ → E} (H : PolyAt N φ) : PolyAt (N + 1) φ := by
  obtain ⟨c, hc⟩ := H
  refine ⟨fun j => if j < N then c j else 0, fun Y => ?_⟩
  rw [hc Y, Finset.sum_range_succ]
  simp only [lt_self_iff_false, ↓reduceIte, smul_zero, add_zero]
  exact Finset.sum_congr rfl fun j hj => by rw [if_pos (Finset.mem_range.mp hj)]
end PolyAt
end Formalism.FourierDecayAlt.P.Qx2
