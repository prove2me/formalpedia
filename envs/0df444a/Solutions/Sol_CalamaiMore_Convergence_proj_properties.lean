-- Prove2me | solution 1 for CalamaiMore.Convergence.proj_properties
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:31:33.14598+00:00
-- url     : https://prove2.me/submissions/da8bf05d-cf1e-4220-b82f-1ffaa5e3c4cb

import Mathlib
import Definitions.Def_CalamaiMore_Convergence_proj
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

/-- Calamai–Moré, Lemma 2.1 (p. 98): (a) the variational inequality of the projection,
(b) monotonicity (strict when the projections differ), (c) nonexpansiveness. -/
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Ω : Set E) (hΩne : Ω.Nonempty) (hΩc : IsClosed Ω) (hΩcv : Convex ℝ Ω) :
    (∀ x : E, ∀ z ∈ Ω, 0 ≤ inner ℝ (proj Ω x - x) (z - proj Ω x)) ∧
    (∀ x y : E, 0 ≤ inner ℝ (proj Ω y - proj Ω x) (y - x) ∧
      (proj Ω y ≠ proj Ω x → 0 < inner ℝ (proj Ω y - proj Ω x) (y - x))) ∧
    (∀ x y : E, ‖proj Ω y - proj Ω x‖ ≤ ‖y - x‖) := by
  have hfirm (x y : E) : ‖proj Ω y - proj Ω x‖ ^ 2 ≤ ⟪proj Ω y - proj Ω x, y - x⟫_ℝ := by
    have hpx := projection_spec Ω hΩne hΩc hΩcv x
    have hpy := projection_spec Ω hΩne hΩc hΩcv y
    have h1 := hpx.2 (proj Ω y) hpy.1
    have h2 := hpy.2 (proj Ω x) hpx.1
    simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right] at *
    simp only [real_inner_comm (proj Ω x) x, real_inner_comm (proj Ω y) x,
      real_inner_comm (proj Ω x) y, real_inner_comm (proj Ω y) y,
      real_inner_comm (proj Ω y) (proj Ω x)] at *
    linarith
  refine ⟨?_, ?_, ?_⟩
  · intro x z hz
    have hp := (projection_spec Ω hΩne hΩc hΩcv x).2 z hz
    rw [← neg_sub x _, inner_neg_left]
    linarith
  · intro x y
    refine ⟨(sq_nonneg _).trans (hfirm x y), ?_⟩
    intro hne
    have hp : 0 < ‖proj Ω y - proj Ω x‖ ^ 2 :=
      sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
    exact hp.trans_le (hfirm x y)
  · intro x y
    have h1 := hfirm x y
    have h2 := real_inner_le_norm (proj Ω y - proj Ω x) (y - x)
    have hn1 := norm_nonneg (proj Ω y - proj Ω x)
    have hn2 := norm_nonneg (y - x)
    nlinarith

end CalamaiMore.Convergence
