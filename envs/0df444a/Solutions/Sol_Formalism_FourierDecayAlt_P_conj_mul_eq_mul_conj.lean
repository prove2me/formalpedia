-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.conj_mul_eq_mul_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:43:57.575429+00:00
-- url     : https://prove2.me/submissions/d2950fb7-80e9-45d8-98c8-5c41ce64d909

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RelevantMonotoneOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InverseSplitting

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open C2x2 InverseSplitting
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution {m : ℕ} (P X Y : Matrix (Fin m) (Fin m) ℂ) (hP : IsUnit P.det) :
    P⁻¹ * (X * Y) * P = (P⁻¹ * X * P) * (P⁻¹ * Y * P) := by
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hP]
end Formalism.FourierDecayAlt.P
