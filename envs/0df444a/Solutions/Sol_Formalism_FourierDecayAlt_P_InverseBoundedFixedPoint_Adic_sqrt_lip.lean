-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.Adic.sqrt_lip
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:23:44.541049+00:00
-- url     : https://prove2.me/submissions/5b1bc556-54e2-4422-bfe2-b87499b4ed04

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SubmoduleMultiplication
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_Adic_nak
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_quad_diff

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
theorem _root_.solution (h : Adic R ϖ) {G N N' Y Y' : Matrix (Fin m) (Fin m) K}
    (hG : ∀ i j, G i j ∈ R) (hY : ∀ i j, Y i j ∈ R) (hY' : ∀ i j, Y' i j ∈ R)
    (e : Y = N - (ϖ : K) • (Y * G * Y)) (e' : Y' = N' - (ϖ : K) • (Y' * G * Y'))
    (Λ : Submodule R K) (hN : MemM Λ (N - N')) : MemM Λ (Y - Y') := by
  have := h.nak (ι := Fin m × Fin m) (fun p => (Y - Y') p.1 p.2) Λ (fun Λ' hd p => by
    have h1 := quad_diff (Λ := Λ') hG hY hY' (fun i j => hd (i, j))
    refine ⟨_, hN p.1 p.2, _, Λ'.neg_mem (h1 p.1 p.2), ?_⟩
    have e1 := congrFun (congrFun e p.1) p.2
    have e2 := congrFun (congrFun e' p.1) p.2
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at e1 e2 ⊢
    linear_combination e1 - e2)
  exact fun i j => this (i, j)
end Adic
end Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
