-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux4.skewOf_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:39:32.210079+00:00
-- url     : https://prove2.me/submissions/68e7f5b3-c29f-4066-aab3-5fdcda3bcc1e

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux4
variable {k j ρ : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux4
theorem _root_.solution (q : (G.UT j → ℂ) × (Fin j → ℝ)) : (skewOf q)ᴴ = -skewOf q := by
  unfold skewOf
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose,
    Matrix.diagonal_conjTranspose]
  have : (star fun i => Complex.I * ((q.2 i : ℝ) : ℂ)) = (fun i => -(Complex.I * ((q.2 i : ℝ) : ℂ))) := by
    funext i
    simp [Complex.conj_ofReal]
  rw [this, ← Matrix.diagonal_neg]
  abel
end Formalism.FourierDecayAlt.P.Ux4
