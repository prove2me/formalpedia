-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x8.solveL
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:19:58.459017+00:00
-- url     : https://prove2.me/submissions/08a1be7e-d6f0-4e66-98f9-9d6d3f354fb1

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
    (h : (N.map φ) *ᵥ μ = w) (hw : ∀ a, w a ∈ I) : ∀ a, μ a ∈ I := by
  have e : μ = (N⁻¹.map φ) *ᵥ w := by
    rw [← h, Matrix.mulVec_mulVec, ← Matrix.map_mul, Matrix.nonsing_inv_mul N hN]
    simp
  intro a
  rw [e]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  exact sum_mem fun c _ => hI _ _ (hw c)
end Formalism.FourierDecayAlt.P.S3x8
