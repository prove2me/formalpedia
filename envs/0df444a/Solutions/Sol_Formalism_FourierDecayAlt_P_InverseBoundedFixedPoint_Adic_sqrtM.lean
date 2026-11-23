-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.Adic.sqrtM
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:13.709828+00:00
-- url     : https://prove2.me/submissions/562170da-c7e2-4846-ae38-8c4201ea9814

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SubmoduleMultiplication
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_Adic_fp
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_int_mul
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
theorem _root_.solution (h : Adic R ϖ) (G N : Matrix (Fin m) (Fin m) K) (hG : ∀ i j, G i j ∈ R)
    (hN : ∀ i j, N i j ∈ R) :
    ∃ Y : Matrix (Fin m) (Fin m) K, (∀ i j, Y i j ∈ R) ∧ Y = N - (ϖ : K) • (Y * G * Y) := by
  have := h.t2
  have hXe : {Y : Matrix (Fin m) (Fin m) K | ∀ i j, Y i j ∈ R} =
      Set.pi Set.univ fun _ : Fin m => Set.pi Set.univ fun _ : Fin m => (R : Set K) := by
    ext Y
    exact ⟨fun hY i _ j _ => hY i j, fun hY i j => hY i trivial j trivial⟩
  have hXc : IsCompact {Y : Matrix (Fin m) (Fin m) K | ∀ i j, Y i j ∈ R} := by
    rw [hXe]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => h.isCompact
  obtain ⟨Y, hY, e⟩ := h.fp (E := Matrix (Fin m) (Fin m) K) (ι := Fin m × Fin m)
    (fun p Y => Y p.1 p.2) (fun p => continuous_id.matrix_elem p.1 p.2)
    (fun x y hxy => Matrix.ext fun i j => hxy (i, j))
    {Y | ∀ i j, Y i j ∈ R} hXc hXc.isClosed ⟨0, fun i j => R.zero_mem⟩ (fun x hx p => hx p.1 p.2)
    (fun Y => N - (ϖ : K) • (Y * G * Y))
    (fun Y hY i j => R.sub_mem (hN i j) (R.mul_mem h.mem (int_mul (int_mul hY hG) hY i j)))
    (fun n Y hY Y' hY' hd p => by
      have h1 := quad_diff (Λ := sm ((ϖ : K) ^ n) (Rs R)) hG hY hY' (fun i j => hd (i, j))
      obtain ⟨l, hl, e⟩ := h1 p.1 p.2
      refine ⟨-l, R.neg_mem hl, ?_⟩
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at e ⊢
      linear_combination (-(ϖ : K)) * e)
  exact ⟨Y, hY, e.symm⟩
end Adic
end Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
