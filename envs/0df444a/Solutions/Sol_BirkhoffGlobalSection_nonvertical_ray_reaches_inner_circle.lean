-- Prove2me | solution 1 for BirkhoffGlobalSection.nonvertical_ray_reaches_inner_circle
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T10:21:05.811189+00:00
-- url     : https://prove2.me/submissions/d23e9787-232b-49e2-a501-7d3f6caa44a1

import Mathlib
import Definitions.Def_BirkhoffGlobalSection

open BirkhoffGlobalSection

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (x : Phase) (hx : 0 < zNormSq x) :
    ∃ R : ℝ, 0 < R ∧
      ((leviCivitaPosition 0 (fun i : Fin 4 => R * x i)) 0) ^ 2 +
        ((leviCivitaPosition 0 (fun i : Fin 4 => R * x i)) 1) ^ 2 = r ^ 2 ∧
      ∀ t : ℝ, 0 ≤ t → t ≤ R →
        0 < secondCollisionDistanceSq (fun i : Fin 4 => t * x i) := by
  let Z : ℝ := zNormSq x
  let R : ℝ := Real.sqrt (r / (2 * Z))
  have hden : 0 < 2 * Z := by dsimp [Z]; positivity
  have hquot : 0 < r / (2 * Z) := div_pos hr hden
  have hR : 0 < R := Real.sqrt_pos.2 hquot
  have hRsq : R ^ 2 = r / (2 * Z) := Real.sq_sqrt (le_of_lt hquot)
  have hRn : 2 * R ^ 2 * Z = r := by
    rw [hRsq]
    have hZne : Z ≠ 0 := ne_of_gt hx
    field_simp [hZne] <;> ring
  have hgeom (t : ℝ) :
      ((leviCivitaPosition 0 (fun i : Fin 4 => t * x i)) 0) ^ 2 +
        ((leviCivitaPosition 0 (fun i : Fin 4 => t * x i)) 1) ^ 2 =
        (2 * t ^ 2 * Z) ^ 2 := by
    dsimp [leviCivitaPosition, Z, zNormSq]
    ring
  refine ⟨R, hR, ?_, ?_⟩
  · rw [hgeom, hRn]
  · intro t ht0 htR
    have htSq : t ^ 2 ≤ R ^ 2 :=
      (sq_le_sq₀ ht0 (le_of_lt hR)).2 htR
    have hbound : 0 ≤ 2 * t ^ 2 * Z := by
      dsimp [Z, zNormSq]
      positivity
    have htbound : 2 * t ^ 2 * Z ≤ r := by
      nlinarith [mul_nonneg (sub_nonneg.mpr htSq) (le_of_lt hx), hRn]
    have hqSq : (2 * t ^ 2 * Z) ^ 2 ≤ r ^ 2 :=
      (sq_le_sq₀ hbound (le_of_lt hr)).2 htbound
    have hrSq : r ^ 2 < 1 := by
      nlinarith [mul_pos hr (sub_pos.mpr hr1)]
    let a : ℝ := (leviCivitaPosition 0 (fun i : Fin 4 => t * x i)) 0
    let b : ℝ := (leviCivitaPosition 0 (fun i : Fin 4 => t * x i)) 1
    have hnorm : a ^ 2 + b ^ 2 < 1 := by
      have hg := hgeom t
      change a ^ 2 + b ^ 2 = (2 * t ^ 2 * Z) ^ 2 at hg
      linarith
    have hdist : secondCollisionDistanceSq (fun i : Fin 4 => t * x i) =
        (a - 1) ^ 2 + b ^ 2 := by
      dsimp [secondCollisionDistanceSq, a, b, leviCivitaPosition]
      ring
    rw [hdist]
    by_contra hn
    have ha : a = 1 := by nlinarith [sq_nonneg b, sq_nonneg (a - 1)]
    have hb : b = 0 := by nlinarith [sq_nonneg (a - 1), sq_nonneg b]
    rw [ha, hb] at hnorm
    norm_num at hnorm
