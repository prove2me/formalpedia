-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.conj_inv_eq_inv_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:47:53.354934+00:00
-- url     : https://prove2.me/submissions/d357d84c-490a-4bdc-9e6b-7f7d6e7f8a19

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
theorem _root_.solution {m : ℕ} (P X : Matrix (Fin m) (Fin m) ℂ) (hP : IsUnit P.det) :
    (P⁻¹ * X * P)⁻¹ = P⁻¹ * X⁻¹ * P := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv P hP, Matrix.mul_assoc]
end Formalism.FourierDecayAlt.P
