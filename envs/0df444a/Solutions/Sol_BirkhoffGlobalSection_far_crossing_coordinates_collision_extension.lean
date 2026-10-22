-- Prove2me | solution 1 for BirkhoffGlobalSection.far_crossing_coordinates_collision_extension
-- status  : ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-26T22:01:00.9841+00:00
-- url     : https://prove2.me/submissions/c5fec275-e73e-4052-8906-57514b5cfc85

import Definitions.Def_BirkhoffShootingCoordinates
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

open BirkhoffGlobalSection

/- The coordinate cancellation and strict bound below are adapted from Mazecto's
accepted sketch of `BirkhoffGlobalSection.birkhoff_far_arc_end` on Prove2Me.
This file isolates its collision chart as a reusable, self-contained theorem. -/

private noncomputable def Vx (s : Phase) : ℝ := (s 2 * s 0 - s 3 * s 1) / (s 0 ^ 2 + s 1 ^ 2) - 4 * s 0 * s 1

private noncomputable def Vy (μ : ℝ) (s : Phase) : ℝ :=
  (s 2 * s 1 + s 3 * s 0) / (s 0 ^ 2 + s 1 ^ 2) + 2 * (s 0 ^ 2 - s 1 ^ 2) - μ


private lemma jv_eq (μ : ℝ) (s : Phase) :
    jacobiVelocity (leviCivitaToJacobi μ s) 0 = Vx s ∧
      jacobiVelocity (leviCivitaToJacobi μ s) 1 = Vy μ s := by
  constructor <;>
    simp [jacobiVelocity, leviCivitaToJacobi, leviCivitaPosition, leviCivitaMomentum, zNormSq, Vx, Vy] <;>
    ring

private lemma relPos_eq (μ : ℝ) (s : Phase) :
    relativePosition μ s 0 = 2 * (s 0 ^ 2 - s 1 ^ 2) ∧ relativePosition μ s 1 = 4 * s 0 * s 1 := by
  simp [relativePosition, leviCivitaPosition]


private lemma coords_eq (μ : ℝ) : shootingCoordinates μ = fun s : Phase =>
    (Vy μ s / Real.sqrt (Vx s ^ 2 + Vy μ s ^ 2), -(4 * s 0 * s 1)) := by
  funext s
  simp only [shootingCoordinates, (jv_eq μ s).1, (jv_eq μ s).2, (relPos_eq μ s).2]


private noncomputable def Gfar (μ α p q : ℝ) : ℝ :=
  (p - q - 2 * α * μ) / Real.sqrt ((8 * α ^ 3 - p - q) ^ 2 + (p - q - 2 * α * μ) ^ 2)

private lemma coords_far_cross (μ : ℝ) (s : Phase) (α : ℝ) (hα : 0 < α) (h0 : s 0 = -α) (h1 : s 1 = α) :
    shootingCoordinates μ s = (Gfar μ α (s 2) (s 3), 4 * α ^ 2) := by
  rw [coords_eq]
  simp only [Vx, Vy, Gfar, h0, h1]
  congr 1
  · have e1 : (s 2 * -α - s 3 * α) / ((-α) ^ 2 + α ^ 2) - 4 * -α * α =
        (8 * α ^ 3 - s 2 - s 3) / (2 * α) := by field_simp; ring
    have e2 : (s 2 * α + s 3 * -α) / ((-α) ^ 2 + α ^ 2) + 2 * ((-α) ^ 2 - α ^ 2) - μ =
        (s 2 - s 3 - 2 * α * μ) / (2 * α) := by field_simp; ring
    rw [e1, e2, div_pow, div_pow, ← add_div, Real.sqrt_div' _ (by positivity),
      Real.sqrt_sq (by positivity), div_div_div_cancel_right₀ (by positivity)]
  · ring


private lemma Gfar_collision_bound (μ w0 w1 : ℝ) (h0 : 0 < w0) (h1 : w1 < 0) :
    Real.sqrt 2 / 2 < Gfar μ 0 w0 w1 := by
  have e : Gfar μ 0 w0 w1 = (w0 - w1) / Real.sqrt ((w0 + w1) ^ 2 + (w0 - w1) ^ 2) := by
    unfold Gfar; congr 1 <;> ring_nf
  rw [e]
  set X := (w0 + w1) ^ 2 + (w0 - w1) ^ 2 with hX
  have hXpos : 0 < X := by
    have : 0 < (w0 - w1) ^ 2 := by nlinarith
    rw [hX]; nlinarith [sq_nonneg (w0 + w1)]
  set D := Real.sqrt X with hD
  have hDpos : 0 < D := Real.sqrt_pos.2 hXpos
  have hD2 : D ^ 2 = X := Real.sq_sqrt hXpos.le
  have hs2 : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num
  have hs0 : 0 < Real.sqrt 2 / 2 := by positivity
  set a := (w0 - w1) / D with ha
  have haD : a * D = w0 - w1 := by rw [ha]; field_simp
  have hpos : 0 < a := div_pos (by linarith) hDpos
  have hsq : a ^ 2 * X = (w0 - w1) ^ 2 := by rw [← hD2, ← mul_pow, haD]
  have h2 : 1 / 2 < a ^ 2 := by
    by_contra h
    have h : a ^ 2 ≤ 1 / 2 := le_of_not_gt h
    have : a ^ 2 * X ≤ 1 / 2 * X := mul_le_mul_of_nonneg_right h hXpos.le
    nlinarith [mul_pos h0 (neg_pos.2 h1)]
  nlinarith


theorem solution (μ : ℝ) (s₀ : Phase) (hz0 : s₀ 0 = 0) (hz1 : s₀ 1 = 0)
    (hp : 0 < s₀ 2) (hq : s₀ 3 < 0) :
    ∃ H : Phase → ℝ × ℝ, ContinuousAt H s₀ ∧ (H s₀).2 = 0 ∧
      Real.sqrt 2 / 2 < (H s₀).1 ∧
      ∀ s : Phase, 0 < s 1 → s 0 = -s 1 → shootingCoordinates μ s = H s := by
  let H : Phase → ℝ × ℝ := fun s => (Gfar μ (s 1) (s 2) (s 3), 4 * s 1 ^ 2)
  have hcont : ContinuousAt H s₀ := by
    have hden : Real.sqrt ((8 * s₀ 1 ^ 3 - s₀ 2 - s₀ 3) ^ 2 +
        (s₀ 2 - s₀ 3 - 2 * s₀ 1 * μ) ^ 2) ≠ 0 := by
      apply (Real.sqrt_pos.2 _).ne'
      rw [hz1]
      have : 0 < (s₀ 2 - s₀ 3) ^ 2 := by
        have : 0 < s₀ 2 - s₀ 3 := by linarith
        positivity
      nlinarith [sq_nonneg (8 * (0:ℝ) ^ 3 - s₀ 2 - s₀ 3)]
    apply ContinuousAt.prodMk
    · unfold Gfar
      exact ContinuousAt.div (by fun_prop)
        ((by fun_prop : ContinuousAt (fun s : Phase => (8 * s 1 ^ 3 - s 2 - s 3) ^ 2 +
          (s 2 - s 3 - 2 * s 1 * μ) ^ 2) s₀).sqrt) hden
    · exact (continuous_const.mul ((continuous_apply 1).pow 2)).continuousAt
  refine ⟨H, hcont, ?_, ?_, ?_⟩
  · simp [H, hz1]
  · simpa [H, hz1] using Gfar_collision_bound μ (s₀ 2) (s₀ 3) hp hq
  · intro s hs hdiag
    exact coords_far_cross μ s (s 1) hs hdiag rfl
