-- Prove2me | solution 1 for DistInterpRO.Shrinkage.pointwise_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:04:51.682392+00:00
-- url     : https://prove2.me/submissions/f6dfdcb1-b46b-41e7-8d75-f5e706b900e7

import Mathlib
import Definitions.Def_DistInterpRO_Shrinkage_Model

open MeasureTheory
open scoped Pointwise

namespace DistInterpRO.Shrinkage

lemma aux_ps_1d (φ φ' φ'' : ℝ → ℝ) (M : ℝ) (h1 : ∀ t, HasDerivAt φ (φ' t) t)
    (h2 : ∀ t, HasDerivAt φ' (φ'' t) t) (h3 : ∀ t, 0 ≤ φ'' t + M) (α : ℝ)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    φ α ≤ (1 - α) * φ 0 + α * φ 1 + M * (α * (1 - α)) / 2 := by
  set ψ : ℝ → ℝ := fun t => φ t + M / 2 * t ^ 2 with hψ
  have hd1 : ∀ t, HasDerivAt ψ (φ' t + M * t) t := fun t => by
    have := (h1 t).add ((hasDerivAt_pow 2 t).const_mul (M / 2))
    refine this.congr_deriv ?_
    push_cast
    ring
  have hd2 : ∀ t, HasDerivAt (fun t => φ' t + M * t) (φ'' t + M) t := fun t => by
    have := (h2 t).add ((hasDerivAt_id t).const_mul M)
    refine this.congr_deriv ?_
    simp
  have hconv : ConvexOn ℝ Set.univ ψ := by
    refine convexOn_of_hasDerivWithinAt2_nonneg (f' := fun t => φ' t + M * t)
      (f'' := fun t => φ'' t + M) convex_univ ?_ ?_ ?_ ?_
    · intro t _
      exact (hd1 t).continuousAt.continuousWithinAt
    · intro t _
      exact (hd1 t).hasDerivWithinAt
    · intro t _
      exact (hd2 t).hasDerivWithinAt
    · intro t _
      exact h3 t
  have key := hconv.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ)) (by linarith : 0 ≤ 1 - α)
    hα0 (by ring)
  simp only [hψ, smul_eq_mul] at key
  have e : (1 - α) * 0 + α * 1 = α := by ring
  rw [e] at key
  nlinarith [key]

lemma aux_ps_line {m : ℕ} (F : EuclideanSpace ℝ (Fin m) → ℝ)
    (hF1 : Differentiable ℝ F) (hF2 : Differentiable ℝ (fderiv ℝ F))
    (x₀ x₁ : EuclideanSpace ℝ (Fin m)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F (x₀ + s • x₁)) (fderiv ℝ F (x₀ + t • x₁) x₁) t ∧
    HasDerivAt (fun s : ℝ => fderiv ℝ F (x₀ + s • x₁) x₁)
      (fderiv ℝ (fderiv ℝ F) (x₀ + t • x₁) x₁ x₁) t := by
  have hl : HasDerivAt (fun s : ℝ => x₀ + s • x₁) x₁ t := by
    have := ((hasDerivAt_id t).smul_const x₁).const_add x₀
    simpa using this
  constructor
  · exact (hF1 (x₀ + t • x₁)).hasFDerivAt.comp_hasDerivAt t hl
  · have hc := (hF2 (x₀ + t • x₁)).hasFDerivAt.comp_hasDerivAt t hl
    have := hc.clm_apply (hasDerivAt_const t x₁)
    simpa using this

end DistInterpRO.Shrinkage

open DistInterpRO.Shrinkage
open MeasureTheory
open scoped Pointwise

theorem solution {m : ℕ} {V : Type*} (f : V → EuclideanSpace ℝ (Fin m) → ℝ) (v : V)
    (x₀ : EuclideanSpace ℝ (Fin m)) (Δ : Set (EuclideanSpace ℝ (Fin m))) (hΔc : IsCompact Δ)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (h : ℝ) (hh : 0 ≤ h) (hf : HasBoundedHessian (f v) h)
    (x₁ : EuclideanSpace ℝ (Fin m)) (hx₁ : x₁ ∈ Δ) :
    (1 - α) * f v x₀ + α * f v (x₀ + x₁) - α * devRadius Δ ^ 2 * h ≤ f v (x₀ + α • x₁) ∧
      f v (x₀ + α • x₁) ≤ (1 - α) * f v x₀ + α * f v (x₀ + x₁) + α * devRadius Δ ^ 2 * h := by
  obtain ⟨hF1, hF2, hH⟩ := hf
  set F := f v with hFdef
  set M := h * ‖x₁‖ ^ 2 with hM
  have hline := aux_ps_line F hF1 hF2 x₀ x₁
  -- norm bound
  have hbdd : BddAbove ((fun x => ‖x‖) '' Δ) := (hΔc.image continuous_norm).bddAbove
  have hnD : ‖x₁‖ ≤ devRadius Δ := le_csSup hbdd ⟨x₁, hx₁, rfl⟩
  have hn0 : 0 ≤ ‖x₁‖ := norm_nonneg _
  have hsq : ‖x₁‖ ^ 2 ≤ devRadius Δ ^ 2 := pow_le_pow_left₀ hn0 hnD 2
  have hMb : M * (α * (1 - α)) / 2 ≤ α * devRadius Δ ^ 2 * h := by
    have h1 : M ≤ h * devRadius Δ ^ 2 := by
      rw [hM]; exact mul_le_mul_of_nonneg_left hsq hh
    have hM0 : 0 ≤ M := by rw [hM]; positivity
    have hA : 0 ≤ α * (1 - α) / 2 := by
      have : 0 ≤ 1 - α := by linarith
      positivity
    have hA1 : α * (1 - α) / 2 ≤ α := by nlinarith
    calc M * (α * (1 - α)) / 2 = M * (α * (1 - α) / 2) := by ring
      _ ≤ (h * devRadius Δ ^ 2) * α := by
          apply mul_le_mul h1 hA1 hA
          positivity
      _ = α * devRadius Δ ^ 2 * h := by ring
  have hs0 : F (x₀ + (0 : ℝ) • x₁) = F x₀ := by simp
  have hs1 : F (x₀ + (1 : ℝ) • x₁) = F (x₀ + x₁) := by simp
  constructor
  · -- lower bound: apply 1d lemma to -g
    have := aux_ps_1d (fun s => -F (x₀ + s • x₁)) (fun s => -fderiv ℝ F (x₀ + s • x₁) x₁)
      (fun s => -fderiv ℝ (fderiv ℝ F) (x₀ + s • x₁) x₁ x₁) M
      (fun t => (hline t).1.neg) (fun t => (hline t).2.neg)
      (fun t => by
        have := hH (x₀ + t • x₁) x₁
        have := (abs_le.mp this).2
        simp only [hM]; linarith)
      α hα0.le hα1.le
    simp only [hs0, hs1] at this
    linarith
  · have := aux_ps_1d (fun s => F (x₀ + s • x₁)) (fun s => fderiv ℝ F (x₀ + s • x₁) x₁)
      (fun s => fderiv ℝ (fderiv ℝ F) (x₀ + s • x₁) x₁ x₁) M
      (fun t => (hline t).1) (fun t => (hline t).2)
      (fun t => by
        have := hH (x₀ + t • x₁) x₁
        have := (abs_le.mp this).1
        simp only [hM]; linarith)
      α hα0.le hα1.le
    simp only [hs0, hs1] at this
    linarith
