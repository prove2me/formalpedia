-- Prove2me | solution 1 for CalamaiMore.Convergence.step_ratio_antitone
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:33:05.269127+00:00
-- url     : https://prove2.me/submissions/8146f5b5-31b5-4a28-b1ce-3c374ec8318f

import Mathlib
import Definitions.Def_CalamaiMore_Convergence_proj
open scoped InnerProductSpace
noncomputable section
open CalamaiMore.Convergence

private theorem projection_spec {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (C : Set E)
    (hne : C.Nonempty) (hc : IsClosed C) (hcv : Convex ℝ C) (x : E) :
    proj C x ∈ C ∧ ∀ y ∈ C, ⟪x - proj C x, y - proj C x⟫_ℝ ≤ 0 := by
  letI : Nonempty C := hne.to_subtype
  have hb : BddBelow (Set.range (fun y : C => ‖x - y‖)) := ⟨0, by
    rintro _ ⟨y, rfl⟩
    exact norm_nonneg _⟩
  have he : ∃ p ∈ C, ∀ y ∈ C, ‖p - x‖ ≤ ‖y - x‖ := by
    obtain ⟨p, hp, hmin⟩ := exists_norm_eq_iInf_of_complete_convex hne hc.isComplete hcv x
    refine ⟨p, hp, ?_⟩
    intro y hy
    rw [norm_sub_rev p x, norm_sub_rev y x, hmin]
    exact ciInf_le hb ⟨y, hy⟩
  have hraw : proj C x ∈ C ∧ ∀ y ∈ C, ‖proj C x - x‖ ≤ ‖y - x‖ := by
    simpa only [proj, nearestPoint, dif_pos he] using Classical.choose_spec he
  have hp : ∀ y ∈ C, ‖x - proj C x‖ ≤ ‖x - y‖ := by
    intro y hy
    rw [norm_sub_rev x _, norm_sub_rev x y]
    exact hraw.2 y hy
  refine ⟨hraw.1, (norm_eq_iInf_iff_real_inner_le_zero hcv hraw.1).mp ?_⟩
  exact le_antisymm (le_ciInf (fun y => hp y y.2))
    (ciInf_le hb ⟨_, hraw.1⟩)

private theorem projection_descent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (C : Set E) (hne : C.Nonempty) (hc : IsClosed C) (hcv : Convex ℝ C)
    (x g : E) (hx : x ∈ C) (a : ℝ) (ha : 0 < a) :
    ‖proj C (x - a • g) - x‖ ^ 2 / a ≤ ⟪g, x - proj C (x - a • g)⟫_ℝ := by
  have hp := (projection_spec C hne hc hcv (x - a • g)).2 x hx
  rw [div_le_iff₀ ha]
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_comm (proj C (x - a • g)) x] at *
  nlinarith

namespace CalamaiMore.Convergence

/-- Calamai–Moré, Lemma 2.2 (p. 98): for any `x d`, the function
`ψ(α) = ‖P(x + α d) - x‖ / α` is nonincreasing on `α > 0`. -/
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Ω : Set E) (hΩne : Ω.Nonempty) (hΩc : IsClosed Ω) (hΩcv : Convex ℝ Ω)
    (x d : E) :
    AntitoneOn (fun a : ℝ => ‖proj Ω (x + a • d) - x‖ / a) (Set.Ioi 0) := by
  intro a ha b hb hab
  change 0 < a at ha
  change 0 < b at hb
  let u := proj Ω (x + a • d) - x
  let v := proj Ω (x + b • d) - x
  have hpa := projection_spec Ω hΩne hΩc hΩcv (x + a • d)
  have hpb := projection_spec Ω hΩne hΩc hΩcv (x + b • d)
  have h1 : ⟪a • d - u, v - u⟫_ℝ ≤ 0 := by
    convert hpa.2 _ hpb.1 using 1 <;> congr 1 <;> dsimp [u, v] <;> abel
  have h2 : ⟪b • d - v, u - v⟫_ℝ ≤ 0 := by
    convert hpb.2 _ hpa.1 using 1 <;> congr 1 <;> dsimp [u, v] <;> abel
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_comm v u, real_inner_self_eq_norm_sq] at h1 h2
  have h1b := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hb) h1
  have h2a := mul_nonpos_of_nonneg_of_nonpos (le_of_lt ha) h2
  have hcross := mul_le_mul_of_nonneg_left (real_inner_le_norm v u)
    (show 0 ≤ a + b by linarith)
  have hineq : b * ‖u‖ ^ 2 + a * ‖v‖ ^ 2 ≤ (a + b) * ‖u‖ * ‖v‖ := by
    nlinarith
  rw [div_le_div_iff₀ hb ha]
  change ‖v‖ * a ≤ ‖u‖ * b
  by_contra h
  have hbad : b * ‖u‖ < a * ‖v‖ := by linarith
  have hnorm : ‖u‖ < ‖v‖ := by
    have hh := mul_nonneg (sub_nonneg.mpr hab) (norm_nonneg u)
    nlinarith
  have hp := mul_pos (sub_pos.mpr hnorm) (sub_pos.mpr hbad)
  nlinarith


end CalamaiMore.Convergence
