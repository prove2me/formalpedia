-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x8.solveR
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:19:58.767565+00:00
-- url     : https://prove2.me/submissions/aa7e1525-e512-4a0a-874c-3c58c46ac214

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CentreBlockStructure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x8
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det isLowUni_det)
open Formalism.FourierDecayAlt.S3
variable {A F : Type} [CommRing A] [CommRing F]
namespace Formalism.FourierDecayAlt.P.S3x8
theorem _root_.solution (φ : A →+* F) (I : AddSubgroup F) (hI : ∀ a x, x ∈ I → φ a * x ∈ I) {r : ℕ}
    (N : Matrix (Fin r) (Fin r) A) (hN : IsUnit N.det) (μ w : Fin r → F)
    (h : μ ᵥ* (N.map φ) = w) (hw : ∀ a, w a ∈ I) : ∀ a, μ a ∈ I := by
  have e : μ = w ᵥ* (N⁻¹.map φ) := by
    rw [← h, Matrix.vecMul_vecMul, ← Matrix.map_mul, Matrix.mul_nonsing_inv N hN]
    simp
  intro a
  rw [e]
  simp only [Matrix.vecMul, dotProduct, Matrix.map_apply]
  exact sum_mem fun c _ => by rw [mul_comm]; exact hI _ _ (hw c)
end Formalism.FourierDecayAlt.P.S3x8
