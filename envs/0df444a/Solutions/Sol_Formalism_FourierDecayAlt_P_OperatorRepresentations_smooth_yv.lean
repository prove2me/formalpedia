-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OperatorRepresentations.smooth_yv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:58:38.222962+00:00
-- url     : https://prove2.me/submissions/2a33eb06-b1a8-4f83-81ce-b5849113abe1

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_inv_of_uh

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.OperatorRepresentations
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.P.OperatorRepresentations
theorem _root_.solution (z : Fin (2 * r + k + 1) → ℂ) (c : Fin (mdim k r i)) :
    SmoothLev k r i D (fun g => yv k r z i g c) := fun _ _ =>
  ⟨Set.univ, invL k r (fvec k r z i) (posL k r i c), isOpen_univ, Set.mem_univ _,
    (invL k r (fvec k r z i) (posL k r i c)).contDiff.contDiffOn, fun g _ hg => by
      show (g⁻¹ *ᵥ fvec k r z i) (posL k r i c) = ((Hpk k r * gᴴ * Hpk k r) *ᵥ fvec k r z i) (posL k r i c)
      rw [inv_of_uh hg.1]⟩
end Formalism.FourierDecayAlt.P.OperatorRepresentations
