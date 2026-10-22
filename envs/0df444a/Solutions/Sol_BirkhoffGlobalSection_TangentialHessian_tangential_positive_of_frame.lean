-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.tangential_positive_of_frame
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-26T17:40:47.61127+00:00
-- url     : https://prove2.me/submissions/163957e0-6076-411d-9a5b-0416b6dffa23

import Definitions.Def_BirkhoffGlobalSection_TangentialHessian
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic

namespace BirkhoffGlobalSection.TangentialHessian.Sol

open BirkhoffGlobalSection BirkhoffGlobalSection.TangentialHessian Filter Topology

noncomputable section

/-- `g, Ig, Jg, Kg` is an orthogonal basis with all norms equal to `|g|`, so
every vector is recovered from its four coordinates in it. -/
theorem quaternion_frame_expansion (g v : Phase) :
    (g ⬝ᵥ g) • v =
      (g ⬝ᵥ v) • g + ∑ i : Fin 3, (frame g i ⬝ᵥ v) • frame g i := by
  funext k
  fin_cases k <;>
    simp [frame, qI, qJ, qK, dotProduct, Fin.sum_univ_four,
      Fin.sum_univ_three] <;> ring

/-- A linear functional on `Phase` is the dot product with its gradient. -/
theorem clm_apply_eq_grad_dot (L : Phase →L[ℝ] ℝ) (v : Phase) :
    L v = (fun i => L (coordinateVector i)) ⬝ᵥ v := by
  have hv : v = ∑ i : Fin 4, v i • coordinateVector i := by
    funext k
    simp [coordinateVector, Finset.sum_apply]
  conv_lhs => rw [hv]
  simp [map_sum, dotProduct, mul_comm]

theorem fderiv_apply_eq_grad_dot (F : Phase → ℝ) (s v : Phase) :
    fderiv ℝ F s v = grad F s ⬝ᵥ v :=
  clm_apply_eq_grad_dot _ v

/-- The iterated directional derivative in `HasPositiveTangentialHessianOn` is the
second Fréchet derivative `D²F(s)(v,v)` once `F` is `C²` near `s`. -/
theorem second_directional_eq (F : Phase → ℝ) (s v : Phase)
    (hF : ContDiffAt ℝ 2 F s) :
    fderiv ℝ (fun x => fderiv ℝ F x v) s v = fderiv ℝ (fderiv ℝ F) s v v := by
  have hd : DifferentiableAt ℝ (fderiv ℝ F) s :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [fderiv_clm_apply hd (differentiableAt_const v)]
  simp

/-- **Bridge.** If the gradient is nonzero and the `3 × 3` tangential Hessian in the
frame `I∇F, J∇F, K∇F` is positive definite, then the platform condition holds
at `s`. -/
theorem tangential_positive_of_frame (F : Phase → ℝ) (s : Phase)
    (hF : ContDiffAt ℝ 2 F s) (hg : grad F s ≠ 0)
    (hpos : ∀ a : Fin 3 → ℝ, a ≠ 0 →
      0 < ∑ i : Fin 3, ∑ j : Fin 3, a i * a j *
        fderiv ℝ (fderiv ℝ F) s (frame (grad F s) i) (frame (grad F s) j))
    (v : Phase) (hv : v ≠ 0) (hker : fderiv ℝ F s v = 0) :
    0 < fderiv ℝ (fun x => fderiv ℝ F x v) s v := by
  set g := grad F s
  set B := fderiv ℝ (fderiv ℝ F) s
  have hgv : g ⬝ᵥ v = 0 := by rw [← fderiv_apply_eq_grad_dot]; exact hker
  have hgg : 0 < g ⬝ᵥ g := by
    rcases Function.ne_iff.mp hg with ⟨k, hk⟩
    have : 0 < g k * g k := mul_self_pos.mpr hk
    calc 0 < g k * g k := this
      _ ≤ g ⬝ᵥ g := by
        simp only [dotProduct]
        exact Finset.single_le_sum (f := fun i => g i * g i)
          (fun i _ => mul_self_nonneg (g i)) (Finset.mem_univ k)
  set a : Fin 3 → ℝ := fun i => (frame g i ⬝ᵥ v) / (g ⬝ᵥ g)
  have hexp : v = ∑ i : Fin 3, a i • frame g i := by
    have h := quaternion_frame_expansion g v
    rw [hgv, zero_smul, zero_add] at h
    funext k
    have hk := congrFun h k
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at hk ⊢
    have hsplit : ∑ i : Fin 3, a i * frame g i k =
        (g ⬝ᵥ g)⁻¹ * ∑ i : Fin 3, (frame g i ⬝ᵥ v) * frame g i k := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by simp only [a]; ring
    rw [hsplit, ← hk]
    field_simp
  have ha : a ≠ 0 := by
    intro h0
    apply hv
    rw [hexp]
    simp [h0]
  rw [second_directional_eq F s v hF]
  have hsum := hpos a ha
  convert hsum using 1
  conv_lhs => rw [hexp]
  simp only [B, map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply,
    FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end

end BirkhoffGlobalSection.TangentialHessian.Sol

open BirkhoffGlobalSection BirkhoffGlobalSection.TangentialHessian BirkhoffGlobalSection.TangentialHessian.Sol

theorem solution (F : Phase → ℝ) (s : Phase)
    (hF : ContDiffAt ℝ 2 F s) (hg : grad F s ≠ 0)
    (hpos : ∀ a : Fin 3 → ℝ, a ≠ 0 →
      0 < ∑ i : Fin 3, ∑ j : Fin 3, a i * a j *
        fderiv ℝ (fderiv ℝ F) s (frame (grad F s) i) (frame (grad F s) j))
    (v : Phase) (hv : v ≠ 0) (hker : fderiv ℝ F s v = 0) :
    0 < fderiv ℝ (fun x => fderiv ℝ F x v) s v := by
  exact tangential_positive_of_frame F s hF hg hpos v hv hker
