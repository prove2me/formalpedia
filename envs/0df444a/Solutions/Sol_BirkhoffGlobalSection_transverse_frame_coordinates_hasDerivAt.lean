-- Prove2me | solution 1 for BirkhoffGlobalSection.transverse_frame_coordinates_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-05T03:45:54.272861+00:00
-- url     : https://prove2.me/submissions/fd4795d9-8398-4002-bd46-599391d60c4b

import Mathlib
import Definitions.Def_BirkhoffGlobalSection_DynamicalConvexity

/-! # The transverse frame equation

Along a Hamiltonian orbit, write `g` for the gradient, `w` for a variational vector tangent to
the level set, and `H` for the (symmetric) Hessian. In the quaternionic frame `(Jg, Kg)` the
transverse coordinates `z = (w·Jg, w·Kg)` satisfy

`|g|² z' = J₂ [[c + s₁₁, s₁₂], [s₁₂, c + s₂₂]] z + (g·H Ig) z`,

with `c = H(Ig, Ig)` and `sᵢⱼ` the entries of `H` on `(Jg, Kg)`. The components of `w` along
the flow direction `Ig` cancel exactly. -/

namespace BirkhoffGlobalSection.FrameEquation

open BirkhoffGlobalSection BirkhoffGlobalSection.TangentialHessian Matrix

theorem frameEq_mulVec_hasDerivAt (A : Matrix (Fin 4) (Fin 4) ℝ) {g : ℝ → Phase} {g' : Phase} {t : ℝ}
    (hg : HasDerivAt g g' t) : HasDerivAt (fun s => A *ᵥ g s) (A *ᵥ g') t := by
  rw [hasDerivAt_pi]
  intro i
  have hgj := hasDerivAt_pi.1 hg
  have h := HasDerivAt.sum (u := Finset.univ) fun j _ => (hgj j).const_mul (A i j)
  have e : (∑ j ∈ Finset.univ, fun x => A i j * g x j) = fun s => (A *ᵥ g s) i := by
    funext s; simp [Finset.sum_apply, Matrix.mulVec, dotProduct]
  rw [e] at h
  simpa [Matrix.mulVec, dotProduct] using h

theorem frameEq_qI_mulVec (G : Phase) : qI *ᵥ G = ![G 2, G 3, -G 0, -G 1] := by
  funext i; fin_cases i <;> simp [qI, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem frameEq_qJ_mulVec (G : Phase) : qJ *ᵥ G = ![G 1, -G 0, -G 3, G 2] := by
  funext i; fin_cases i <;> simp [qJ, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem frameEq_qK_mulVec (G : Phase) : qK *ᵥ G = ![-G 3, G 2, -G 1, G 0] := by
  funext i; fin_cases i <;> simp [qK, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem frameEq_dotProduct_hasDerivAt {u v : ℝ → Phase} {u' v' : Phase} {t : ℝ}
    (hu : HasDerivAt u u' t) (hv : HasDerivAt v v' t) :
    HasDerivAt (fun s => u s ⬝ᵥ v s) (u' ⬝ᵥ v t + u t ⬝ᵥ v') t := by
  have hu' := hasDerivAt_pi.1 hu
  have hv' := hasDerivAt_pi.1 hv
  have h := HasDerivAt.sum (u := Finset.univ) fun i _ => (hu' i).mul (hv' i)
  have e : (∑ i ∈ Finset.univ, (fun x => u x i) * fun x => v x i) =
      fun s => ∑ i, u s i * v s i := by
    funext s; simp [Finset.sum_apply]
  rw [e] at h
  simpa [dotProduct, Finset.sum_add_distrib] using h

/-- The transverse frame equation (abstract form). -/
theorem frame_eq_core (g w : ℝ → Phase)
    (H : Matrix (Fin 4) (Fin 4) ℝ) (t : ℝ) (hH : H.IsSymm)
    (hg : HasDerivAt g (H *ᵥ (qI *ᵥ g t)) t)
    (hw : HasDerivAt w (qI *ᵥ (H *ᵥ w t)) t)
    (htan : w t ⬝ᵥ g t = 0) (hg0 : g t ≠ 0) :
    HasDerivAt (fun s => transverseFrameCoordinates (g s) (w s))
      ((g t ⬝ᵥ g t)⁻¹ •
        ![-((qJ *ᵥ g t) ⬝ᵥ (H *ᵥ (qK *ᵥ g t)) * (w t ⬝ᵥ (qJ *ᵥ g t))
              + (qK *ᵥ g t) ⬝ᵥ (H *ᵥ (qK *ᵥ g t)) * (w t ⬝ᵥ (qK *ᵥ g t)))
            - (qI *ᵥ g t) ⬝ᵥ (H *ᵥ (qI *ᵥ g t)) * (w t ⬝ᵥ (qK *ᵥ g t))
            + g t ⬝ᵥ (H *ᵥ (qI *ᵥ g t)) * (w t ⬝ᵥ (qJ *ᵥ g t)),
          (qJ *ᵥ g t) ⬝ᵥ (H *ᵥ (qJ *ᵥ g t)) * (w t ⬝ᵥ (qJ *ᵥ g t))
              + (qJ *ᵥ g t) ⬝ᵥ (H *ᵥ (qK *ᵥ g t)) * (w t ⬝ᵥ (qK *ᵥ g t))
            + (qI *ᵥ g t) ⬝ᵥ (H *ᵥ (qI *ᵥ g t)) * (w t ⬝ᵥ (qJ *ᵥ g t))
            + g t ⬝ᵥ (H *ᵥ (qI *ᵥ g t)) * (w t ⬝ᵥ (qK *ᵥ g t))]) t := by
  have hr : g t ⬝ᵥ g t ≠ 0 := by
    intro h; exact hg0 (dotProduct_self_eq_zero.mp h)
  have hJ := frameEq_dotProduct_hasDerivAt hw (frameEq_mulVec_hasDerivAt qJ hg)
  have hK := frameEq_dotProduct_hasDerivAt hw (frameEq_mulVec_hasDerivAt qK hg)
  rw [hasDerivAt_pi]
  intro k
  have hs : ∀ i j, H j i = H i j := fun i j => by
    have := congrFun (congrFun hH i) j; simpa [Matrix.transpose_apply] using this
  set G := g t
  set W := w t
  fin_cases k
  · refine (hJ.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    · simp only [Fin.zero_eta, Pi.smul_apply, Matrix.cons_val_zero, smul_eq_mul]
      rw [eq_inv_mul_iff_mul_eq₀ hr]
      simp only [frameEq_qI_mulVec, frameEq_qJ_mulVec, frameEq_qK_mulVec] at htan ⊢
      simp only [dotProduct, Fin.sum_univ_four, Matrix.mulVec, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
        Matrix.tail_cons] at htan ⊢
      simp only [hs 0 1, hs 0 2, hs 0 3, hs 1 2, hs 1 3, hs 2 3]
      linear_combination
        (-(G 0 * (H 0 0 * (-G 3) + H 0 1 * G 2 + H 0 2 * (-G 1) + H 0 3 * G 0)
            + G 1 * (H 0 1 * (-G 3) + H 1 1 * G 2 + H 1 2 * (-G 1) + H 1 3 * G 0)
            + G 2 * (H 0 2 * (-G 3) + H 1 2 * G 2 + H 2 2 * (-G 1) + H 2 3 * G 0)
            + G 3 * (H 0 3 * (-G 3) + H 1 3 * G 2 + H 2 3 * (-G 1) + H 3 3 * G 0))
          - ((G 1) * (H 0 0 * G 2 + H 0 1 * G 3 + H 0 2 * (-G 0) + H 0 3 * (-G 1))
            + (-G 0) * (H 0 1 * G 2 + H 1 1 * G 3 + H 1 2 * (-G 0) + H 1 3 * (-G 1))
            + (-G 3) * (H 0 2 * G 2 + H 1 2 * G 3 + H 2 2 * (-G 0) + H 2 3 * (-G 1))
            + (G 2) * (H 0 3 * G 2 + H 1 3 * G 3 + H 2 3 * (-G 0) + H 3 3 * (-G 1)))) * htan
    · simp [transverseFrameCoordinates, TangentialHessian.frame]
  · refine (hK.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    · simp only [Fin.mk_one, Pi.smul_apply, Matrix.cons_val_one, Matrix.head_cons, smul_eq_mul]
      rw [eq_inv_mul_iff_mul_eq₀ hr]
      simp only [frameEq_qI_mulVec, frameEq_qJ_mulVec, frameEq_qK_mulVec] at htan ⊢
      simp only [dotProduct, Fin.sum_univ_four, Matrix.mulVec, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
        Matrix.tail_cons] at htan ⊢
      simp only [hs 0 1, hs 0 2, hs 0 3, hs 1 2, hs 1 3, hs 2 3]
      linear_combination
        ((G 0 * (H 0 0 * G 1 + H 0 1 * (-G 0) + H 0 2 * (-G 3) + H 0 3 * G 2)
            + G 1 * (H 0 1 * G 1 + H 1 1 * (-G 0) + H 1 2 * (-G 3) + H 1 3 * G 2)
            + G 2 * (H 0 2 * G 1 + H 1 2 * (-G 0) + H 2 2 * (-G 3) + H 2 3 * G 2)
            + G 3 * (H 0 3 * G 1 + H 1 3 * (-G 0) + H 2 3 * (-G 3) + H 3 3 * G 2))
          - ((-G 3) * (H 0 0 * G 2 + H 0 1 * G 3 + H 0 2 * (-G 0) + H 0 3 * (-G 1))
            + (G 2) * (H 0 1 * G 2 + H 1 1 * G 3 + H 1 2 * (-G 0) + H 1 3 * (-G 1))
            + (-G 1) * (H 0 2 * G 2 + H 1 2 * G 3 + H 2 2 * (-G 0) + H 2 3 * (-G 1))
            + (G 0) * (H 0 3 * G 2 + H 1 3 * G 3 + H 2 3 * (-G 0) + H 3 3 * (-G 1)))) * htan
    · simp [transverseFrameCoordinates, TangentialHessian.frame]

end BirkhoffGlobalSection.FrameEquation

open BirkhoffGlobalSection BirkhoffGlobalSection.TangentialHessian BirkhoffGlobalSection.FrameEquation Matrix in
theorem solution (g w : ℝ → Phase)
    (H : Matrix (Fin 4) (Fin 4) ℝ) (t : ℝ) (hH : H.IsSymm)
    (hg : HasDerivAt g (H *ᵥ (qI *ᵥ g t)) t)
    (hw : HasDerivAt w (qI *ᵥ (H *ᵥ w t)) t)
    (htan : w t ⬝ᵥ g t = 0) (hg0 : g t ≠ 0) :
    HasDerivAt (fun s => transverseFrameCoordinates (g s) (w s))
      ((g t ⬝ᵥ g t)⁻¹ •
        ![-((qJ *ᵥ g t) ⬝ᵥ (H *ᵥ (qK *ᵥ g t)) * (w t ⬝ᵥ (qJ *ᵥ g t))
              + (qK *ᵥ g t) ⬝ᵥ (H *ᵥ (qK *ᵥ g t)) * (w t ⬝ᵥ (qK *ᵥ g t)))
            - (qI *ᵥ g t) ⬝ᵥ (H *ᵥ (qI *ᵥ g t)) * (w t ⬝ᵥ (qK *ᵥ g t))
            + g t ⬝ᵥ (H *ᵥ (qI *ᵥ g t)) * (w t ⬝ᵥ (qJ *ᵥ g t)),
          (qJ *ᵥ g t) ⬝ᵥ (H *ᵥ (qJ *ᵥ g t)) * (w t ⬝ᵥ (qJ *ᵥ g t))
              + (qJ *ᵥ g t) ⬝ᵥ (H *ᵥ (qK *ᵥ g t)) * (w t ⬝ᵥ (qK *ᵥ g t))
            + (qI *ᵥ g t) ⬝ᵥ (H *ᵥ (qI *ᵥ g t)) * (w t ⬝ᵥ (qJ *ᵥ g t))
            + g t ⬝ᵥ (H *ᵥ (qI *ᵥ g t)) * (w t ⬝ᵥ (qK *ᵥ g t))]) t :=
  frame_eq_core g w H t hH hg hw htan hg0
