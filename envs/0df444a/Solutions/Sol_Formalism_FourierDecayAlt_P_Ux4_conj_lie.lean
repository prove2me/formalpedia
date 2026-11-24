-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux4.conj_lie
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:32:31.290251+00:00
-- url     : https://prove2.me/submissions/4886ee94-7bae-4325-8b00-fb3f2e7d25ae

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
theorem _root_.solution {N : ℕ} (n M H : Matrix (Fin N) (Fin N) ℂ) (hu : nᴴ * H * n = H) (hH : Hᴴ = H)
    (hn : n * n⁻¹ = 1) (hM : Mᴴ * H + H * M = 0) :
    (n⁻¹ * M * n)ᴴ * H + H * (n⁻¹ * M * n) = 0 := by
  have h1 : H * n⁻¹ = nᴴ * H := by
    calc H * n⁻¹ = nᴴ * H * n * n⁻¹ := by rw [hu]
      _ = nᴴ * H := by rw [Matrix.mul_assoc (nᴴ * H), hn, Matrix.mul_one]
  have h2 : (n⁻¹)ᴴ * H = H * n := by
    have := congrArg Matrix.conjTranspose h1
    simpa [Matrix.conjTranspose_mul, hH] using this
  calc (n⁻¹ * M * n)ᴴ * H + H * (n⁻¹ * M * n) = nᴴ * Mᴴ * ((n⁻¹)ᴴ * H) + (H * n⁻¹) * M * n := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = nᴴ * (Mᴴ * H + H * M) * n := by
        rw [h2, h1]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hM]; simp
end Formalism.FourierDecayAlt.P.Ux4
