-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OperatorRepresentations.smooth_ybv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:14:29.627015+00:00
-- url     : https://prove2.me/submissions/5eeacaf8-ab32-4b8e-97dd-82cc238f3799

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations

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
    SmoothLev k r i D (fun g => ybv k r z i g c) := fun _ _ =>
  ⟨Set.univ, hrmL k r (bvec (posL k r i c)) (fvec k r z i), isOpen_univ, Set.mem_univ _,
    (hrmL k r (bvec (posL k r i c)) (fvec k r z i)).contDiff.contDiffOn, fun _ _ _ => rfl⟩
end Formalism.FourierDecayAlt.P.OperatorRepresentations
