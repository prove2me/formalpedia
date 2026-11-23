-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.Adic.sqrt_symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:17.382847+00:00
-- url     : https://prove2.me/submissions/63a51ada-8878-425d-b8fd-f62e078f9648

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SubmoduleMultiplication
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_Adic_sqrt_lip

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.A5 Filter Topology Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
variable {R : Subring K} {ϖ : Kˣ} {m : ℕ}
namespace Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
namespace Adic
theorem _root_.solution (h : Adic R ϖ) {G N Y : Matrix (Fin m) (Fin m) K}
    (hG : ∀ i j, G i j ∈ R) (hY : ∀ i j, Y i j ∈ R) (e : Y = N - (ϖ : K) • (Y * G * Y))
    (hGs : Gᵀ = G) (hNs : Nᵀ = N) : Yᵀ = Y := by
  have e' : Yᵀ = N - (ϖ : K) • (Yᵀ * G * Yᵀ) := by
    conv_lhs => rw [e]
    rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_mul,
      hGs, hNs, Matrix.mul_assoc]
  have := h.sqrt_lip hG (fun i j => hY j i) hY e' e ⊥ (fun i j => by simp)
  ext i j
  have h1 : Yᵀ i j - Y i j = 0 := this i j
  exact sub_eq_zero.1 h1
end Adic
end Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
