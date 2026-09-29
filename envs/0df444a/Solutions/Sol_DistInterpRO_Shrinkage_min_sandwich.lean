-- Prove2me | solution 1 for DistInterpRO.Shrinkage.min_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:12:42.25262+00:00
-- url     : https://prove2.me/submissions/eba3140c-c42e-49fb-893f-6b3b877ab473

import Mathlib
import Definitions.Def_DistInterpRO_Shrinkage_Model

open MeasureTheory
open scoped Pointwise

namespace DistInterpRO.Shrinkage

theorem aux_ms_hasDerivAt_line {m : ℕ} (F : EuclideanSpace ℝ (Fin m) → ℝ)
    (hF : Differentiable ℝ F) (x₀ x : EuclideanSpace ℝ (Fin m)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F (x₀ + s • x)) (fderiv ℝ F (x₀ + t • x) x) t := by
  have h1 : HasDerivAt (fun s : ℝ => x₀ + s • x) x t := by
    simpa using ((hasDerivAt_id t).smul_const x).const_add x₀
  exact (hF _).hasFDerivAt.comp_hasDerivAt t h1

theorem aux_ms_hasDerivAt_line2 {m : ℕ} (F : EuclideanSpace ℝ (Fin m) → ℝ)
    (hF : Differentiable ℝ (fderiv ℝ F)) (x₀ x : EuclideanSpace ℝ (Fin m)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => fderiv ℝ F (x₀ + s • x) x)
      (fderiv ℝ (fderiv ℝ F) (x₀ + t • x) x x) t := by
  have h1 : HasDerivAt (fun s : ℝ => x₀ + s • x) x t := by
    simpa using ((hasDerivAt_id t).smul_const x).const_add x₀
  have h2 : HasDerivAt (fun s : ℝ => fderiv ℝ F (x₀ + s • x))
      (fderiv ℝ (fderiv ℝ F) (x₀ + t • x) x) t :=
    (hF _).hasFDerivAt.comp_hasDerivAt t h1
  have h3 := h2.clm_apply (hasDerivAt_const t x)
  simpa using h3

theorem aux_ms_interp {m : ℕ} (F : EuclideanSpace ℝ (Fin m) → ℝ) (h : ℝ) (hh : 0 ≤ h)
    (hF : HasBoundedHessian F h) (x₀ x : EuclideanSpace ℝ (Fin m)) (α : ℝ) (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) :
    |F (x₀ + α • x) - ((1 - α) * F x₀ + α * F (x₀ + x))| ≤ α * (h * ‖x‖ ^ 2) := by
  obtain ⟨hd1, hd2, hb⟩ := hF
  set K := h * ‖x‖ ^ 2 with hK
  have hK0 : 0 ≤ K := mul_nonneg hh (sq_nonneg _)
  have hg' := aux_ms_hasDerivAt_line F hd1 x₀ x
  have hg'' := aux_ms_hasDerivAt_line2 F hd2 x₀ x
  have hbd : ∀ t : ℝ, |fderiv ℝ (fderiv ℝ F) (x₀ + t • x) x x| ≤ K := fun t => hb _ _
  have hsq : ∀ t : ℝ, HasDerivAt (fun s : ℝ => K / 2 * s ^ 2) (K * t) t := by
    intro t
    have := (hasDerivAt_pow 2 t).const_mul (K / 2)
    exact this.congr_deriv (by norm_num; ring)
  have hlin : ∀ t : ℝ, HasDerivAt (fun s : ℝ => K * s) K t := by
    intro t
    simpa using (hasDerivAt_id t).const_mul K
  have hψ1 : ∀ t : ℝ, HasDerivAt (fun s : ℝ => F (x₀ + s • x) + K / 2 * s ^ 2)
      (fderiv ℝ F (x₀ + t • x) x + K * t) t := fun t => (hg' t).add (hsq t)
  have hψ2 : ∀ t : ℝ, HasDerivAt (fun s : ℝ => fderiv ℝ F (x₀ + s • x) x + K * s)
      (fderiv ℝ (fderiv ℝ F) (x₀ + t • x) x x + K) t := fun t => (hg'' t).add (hlin t)
  have hφ1 : ∀ t : ℝ, HasDerivAt (fun s : ℝ => F (x₀ + s • x) - K / 2 * s ^ 2)
      (fderiv ℝ F (x₀ + t • x) x - K * t) t := fun t => (hg' t).sub (hsq t)
  have hφ2 : ∀ t : ℝ, HasDerivAt (fun s : ℝ => fderiv ℝ F (x₀ + s • x) x - K * s)
      (fderiv ℝ (fderiv ℝ F) (x₀ + t • x) x x - K) t := fun t => (hg'' t).sub (hlin t)
  have hconv : ConvexOn ℝ Set.univ (fun t : ℝ => F (x₀ + t • x) + K / 2 * t ^ 2) := by
    refine convexOn_of_hasDerivWithinAt2_nonneg
      (f' := fun t => fderiv ℝ F (x₀ + t • x) x + K * t)
      (f'' := fun t => fderiv ℝ (fderiv ℝ F) (x₀ + t • x) x x + K) convex_univ ?_ ?_ ?_ ?_
    · exact (continuous_iff_continuousAt.mpr fun t => (hψ1 t).continuousAt).continuousOn
    · intro t _
      exact (hψ1 t).hasDerivWithinAt
    · intro t _
      exact (hψ2 t).hasDerivWithinAt
    · intro t _
      have := (abs_le.mp (hbd t)).1
      linarith
  have hconc : ConcaveOn ℝ Set.univ (fun t : ℝ => F (x₀ + t • x) - K / 2 * t ^ 2) := by
    refine concaveOn_of_hasDerivWithinAt2_nonpos
      (f' := fun t => fderiv ℝ F (x₀ + t • x) x - K * t)
      (f'' := fun t => fderiv ℝ (fderiv ℝ F) (x₀ + t • x) x x - K) convex_univ ?_ ?_ ?_ ?_
    · exact (continuous_iff_continuousAt.mpr fun t => (hφ1 t).continuousAt).continuousOn
    · intro t _
      exact (hφ1 t).hasDerivWithinAt
    · intro t _
      exact (hφ2 t).hasDerivWithinAt
    · intro t _
      have := (abs_le.mp (hbd t)).2
      linarith
  have hα1' : 0 ≤ 1 - α := by linarith
  have e1 := hconv.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ)) hα1' hα0 (by ring)
  have e2 := hconc.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ)) hα1' hα0 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, mul_one, zero_smul, one_smul, add_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, one_pow, sub_zero] at e1 e2
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

end DistInterpRO.Shrinkage

open DistInterpRO.Shrinkage

theorem solution {m : ℕ} {V : Type*} (f : V → EuclideanSpace ℝ (Fin m) → ℝ) (v : V)
    (x₀ : EuclideanSpace ℝ (Fin m)) (Δ : Set (EuclideanSpace ℝ (Fin m))) (hΔc : IsCompact Δ)
    (hΔ0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ Δ)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (h : ℝ) (hh : 0 ≤ h) (hf : HasBoundedHessian (f v) h) :
    (1 - α) * f v x₀ + α * (⨅ x : Δ, f v (x₀ + x)) - α * devRadius Δ ^ 2 * h ≤
        (⨅ x : (α • Δ : Set (EuclideanSpace ℝ (Fin m))), f v (x₀ + x)) ∧
      (⨅ x : (α • Δ : Set (EuclideanSpace ℝ (Fin m))), f v (x₀ + x)) ≤
        (1 - α) * f v x₀ + α * (⨅ x : Δ, f v (x₀ + x)) + α * devRadius Δ ^ 2 * h := by
  set F := f v with hFdef
  set D := devRadius Δ with hDdef
  set c := (1 - α) * F x₀ with hcdef
  set E := α * D ^ 2 * h with hEdef
  set L := ⨅ x : Δ, F (x₀ + x) with hLdef
  have hcont : Continuous F := hf.1.continuous
  have hbddΔ : BddBelow (Set.range fun x : Δ => F (x₀ + x)) := by
    refine (hΔc.image (show Continuous (fun x => F (x₀ + x)) from
      hcont.comp (continuous_const_add x₀))).bddBelow.mono ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨x, x.2, rfl⟩
  have hnormle : ∀ x ∈ Δ, ‖x‖ ≤ D := fun x hx =>
    le_csSup (hΔc.image continuous_norm).bddAbove ⟨x, hx, rfl⟩
  have hpt : ∀ x ∈ Δ, |F (x₀ + α • x) - (c + α * F (x₀ + x))| ≤ E := by
    intro x hx
    have h1 := aux_ms_interp F h hh hf x₀ x α hα0.le hα1.le
    have h2 : ‖x‖ ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hnormle x hx) 2
    calc _ ≤ α * (h * ‖x‖ ^ 2) := h1
      _ ≤ α * (h * D ^ 2) := by gcongr
      _ = E := by rw [hEdef]; ring
  have hLle : ∀ x ∈ Δ, L ≤ F (x₀ + x) := fun x hx => ciInf_le hbddΔ ⟨x, hx⟩
  have hlowS : ∀ y : (α • Δ : Set (EuclideanSpace ℝ (Fin m))), c + α * L - E ≤ F (x₀ + y) := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := Set.mem_smul_set.mp hy
    have h1 := (abs_le.mp (hpt x hx)).1
    have h2 := hLle x hx
    have h3 : α * L ≤ α * F (x₀ + x) := mul_le_mul_of_nonneg_left h2 hα0.le
    simp only
    linarith
  have hneS : Nonempty (α • Δ : Set (EuclideanSpace ℝ (Fin m))) :=
    ⟨⟨0, Set.mem_smul_set.mpr ⟨0, hΔ0, smul_zero α⟩⟩⟩
  have hbddS : BddBelow (Set.range fun y : (α • Δ : Set (EuclideanSpace ℝ (Fin m))) =>
      F (x₀ + y)) := ⟨c + α * L - E, by rintro _ ⟨y, rfl⟩; exact hlowS y⟩
  refine ⟨le_ciInf hlowS, ?_⟩
  have hneΔ : Nonempty Δ := ⟨⟨0, hΔ0⟩⟩
  have key : ∀ x : Δ,
      ((⨅ y : (α • Δ : Set (EuclideanSpace ℝ (Fin m))), F (x₀ + y)) - c - E) / α ≤
        F (x₀ + x) := by
    rintro ⟨x, hx⟩
    have hmem : α • x ∈ (α • Δ : Set (EuclideanSpace ℝ (Fin m))) := Set.smul_mem_smul_set hx
    have h1 : (⨅ y : (α • Δ : Set (EuclideanSpace ℝ (Fin m))), F (x₀ + y)) ≤ F (x₀ + α • x) :=
      ciInf_le hbddS ⟨α • x, hmem⟩
    have h2 := (abs_le.mp (hpt x hx)).2
    rw [div_le_iff₀ hα0]
    simp only
    linarith
  have := le_ciInf key
  rw [div_le_iff₀ hα0] at this
  linarith
