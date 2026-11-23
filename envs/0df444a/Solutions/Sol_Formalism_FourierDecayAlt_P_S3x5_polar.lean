-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x5.polar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:49:41.587709+00:00
-- url     : https://prove2.me/submissions/8b7cd28c-f9b6-464e-b68c-be88efe3b7fe

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFrameCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x5
open Matrix
variable {K : Type} [Field K] [Fintype K] [StarRing K]
namespace Formalism.FourierDecayAlt.P.S3x5
theorem _root_.solution (htr : ∃ μ : K, μ + star μ ≠ 0) {ν : Type} [Fintype ν] [DecidableEq ν]
    (J : Matrix ν ν K) (hJ : Jᴴ = J) (W : Submodule K (Matrix ν Unit K))
    (h0 : ∀ v ∈ W, vᴴ * J * v = 0) : ∀ u ∈ W, ∀ v ∈ W, uᴴ * J * v = 0 := by
  intro u hu v hv
  obtain ⟨μ, hμ⟩ := htr
  by_contra hne
  have hz0 : (uᴴ * J * v) () () ≠ 0 := by
    intro h
    apply hne
    ext i j
    exact h
  have hvu : vᴴ * J * u = (uᴴ * J * v)ᴴ := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hJ, Matrix.mul_assoc]
  have h1 := h0 (u + (μ / (uᴴ * J * v) () ()) • v) (W.add_mem hu (W.smul_mem _ hv))
  simp only [conjTranspose_add, conjTranspose_smul, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, h0 u hu, h0 v hv, hvu] at h1
  have h2 := congrFun (congrFun h1 ()) ()
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.zero_apply, conjTranspose_apply, smul_eq_mul,
    zero_add, mul_zero, add_zero] at h2
  apply hμ
  rw [← star_mul', div_mul_cancel₀ _ hz0] at h2
  rw [add_comm]
  exact h2
end Formalism.FourierDecayAlt.P.S3x5
