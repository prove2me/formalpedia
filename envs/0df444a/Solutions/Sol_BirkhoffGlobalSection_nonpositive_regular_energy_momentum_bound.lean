-- Prove2me | solution 1 for BirkhoffGlobalSection.nonpositive_regular_energy_momentum_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T18:24:06.640017+00:00
-- url     : https://prove2.me/submissions/8fe80e73-d907-4d0a-b031-3c216143e002

import Mathlib
import Definitions.Def_BirkhoffGlobalSection
import Theorems.Thm_BirkhoffGlobalSection_quadratic_energy_coordinate_bound

open BirkhoffGlobalSection

theorem solution (μ c R δ : ℝ) (hδ : 0 < δ) :
    ∃ M : ℝ, ∀ s : Phase,
      |s 0| ≤ R → |s 1| ≤ R →
      δ ≤ secondCollisionDistanceSq s →
      leviCivitaHamiltonian μ c s ≤ 0 →
      |s 2| ≤ M ∧ |s 3| ≤ M := by
  let d0 : ℝ := Real.sqrt δ
  have hd0 : 0 < d0 := Real.sqrt_pos.2 hδ
  have hcoeff : ∃ M : ℝ, 0 ≤ M ∧ ∀ s : Phase,
      |s 0| ≤ R → |s 1| ≤ R →
      δ ≤ secondCollisionDistanceSq s →
      |-(2 * zNormSq s + μ) * s 1| ≤ M ∧
      |(2 * zNormSq s - μ) * s 0| ≤ M ∧
      |c * zNormSq s - (1 - μ) / 2 -
        μ * zNormSq s / Real.sqrt (secondCollisionDistanceSq s)| ≤ M := by
    let Rbox : ℝ := |R| + 1
    let T : ℝ := 2 * Rbox ^ 2
    let P : ℝ := (2 * T + |μ|) * Rbox
    let Q : ℝ := |c| * T + (1 + |μ|) / 2 + |μ| * T / d0
    have hR : 0 ≤ Rbox := by dsimp [Rbox]; positivity
    have hT : 0 ≤ T := by dsimp [T]; positivity
    have hP : 0 ≤ P := by dsimp [P]; positivity
    have hQ : 0 ≤ Q := by dsimp [Q]; positivity
    refine ⟨max P Q, le_max_of_le_left hP, ?_⟩
    intro s hx hy hD
    have hd : d0 ≤ Real.sqrt (secondCollisionDistanceSq s) := Real.sqrt_le_sqrt hD
    let Z : ℝ := zNormSq s
    let d : ℝ := Real.sqrt (secondCollisionDistanceSq s)
    have hdpos : 0 < d := lt_of_lt_of_le hd0 hd
    have hZnonneg : 0 ≤ Z := by dsimp [Z, zNormSq]; positivity
    have hxR : |s 0| ≤ Rbox := by dsimp [Rbox]; linarith [le_abs_self R]
    have hyR : |s 1| ≤ Rbox := by dsimp [Rbox]; linarith [le_abs_self R]
    have hxSq : (s 0) ^ 2 ≤ Rbox ^ 2 := by
      have h := (sq_le_sq₀ (abs_nonneg (s 0)) hR).mpr hxR
      simpa only [sq_abs] using h
    have hySq : (s 1) ^ 2 ≤ Rbox ^ 2 := by
      have h := (sq_le_sq₀ (abs_nonneg (s 1)) hR).mpr hyR
      simpa only [sq_abs] using h
    have hZ : Z ≤ T := by dsimp [Z, T, zNormSq]; linarith
    have htwo : |2 * Z| = 2 * Z := abs_of_nonneg (by positivity)
    have hplus : |2 * Z + μ| ≤ 2 * T + |μ| := by
      calc
        _ ≤ |2 * Z| + |μ| := abs_add_le _ _
        _ = 2 * Z + |μ| := by rw [htwo]
        _ ≤ 2 * T + |μ| := by linarith
    have hminus : |2 * Z - μ| ≤ 2 * T + |μ| := by
      calc
        _ ≤ |2 * Z| + |μ| := by
          simpa only [sub_eq_add_neg, abs_neg] using
            (abs_add_le (2 * Z) (-μ))
        _ = 2 * Z + |μ| := by rw [htwo]
        _ ≤ 2 * T + |μ| := by linarith
    have hA : |-(2 * Z + μ) * s 1| ≤ P := by
      rw [abs_mul, abs_neg]
      exact mul_le_mul hplus hyR (abs_nonneg _) (by positivity)
    have hB : |(2 * Z - μ) * s 0| ≤ P := by
      rw [abs_mul]
      exact mul_le_mul hminus hxR (abs_nonneg _) (by positivity)
    have hnum : |μ| * Z ≤ |μ| * T :=
      mul_le_mul_of_nonneg_left hZ (abs_nonneg μ)
    have hgrav : |μ| * Z / d ≤ |μ| * T / d0 := by
      apply (div_le_div_iff₀ hdpos hd0).2
      calc
        |μ| * Z * d0 ≤ |μ| * T * d0 :=
          mul_le_mul_of_nonneg_right hnum (le_of_lt hd0)
        _ ≤ |μ| * T * d :=
          mul_le_mul_of_nonneg_left hd (by positivity)
    have hcZ : |c| * Z ≤ |c| * T :=
      mul_le_mul_of_nonneg_left hZ (abs_nonneg c)
    have honeμ : |1 - μ| ≤ 1 + |μ| := by
      calc
        _ ≤ |(1 : ℝ)| + |μ| := by
          simpa only [sub_zero, zero_sub, abs_neg] using
            (abs_sub_le (1 : ℝ) 0 μ)
        _ = 1 + |μ| := by norm_num
    have hK : |c * Z - (1 - μ) / 2 - μ * Z / d| ≤ Q := by
      have htri : |c * Z - (1 - μ) / 2 - μ * Z / d| ≤
          |c| * Z + |1 - μ| / 2 + |μ| * Z / d := by
        calc
          _ ≤ |c * Z - (1 - μ) / 2| + |μ * Z / d| := by
            simpa only [sub_zero, zero_sub, abs_neg] using
              (abs_sub_le (c * Z - (1 - μ) / 2) 0 (μ * Z / d))
          _ ≤ (|c * Z| + |(1 - μ) / 2|) + |μ * Z / d| := by
            gcongr
            simpa only [sub_zero, zero_sub, abs_neg] using
              (abs_sub_le (c * Z) 0 ((1 - μ) / 2))
          _ = |c| * Z + |1 - μ| / 2 + |μ| * Z / d := by
            simp only [abs_mul, abs_div, abs_of_nonneg hZnonneg,
              abs_of_nonneg (le_of_lt hdpos)]
            norm_num
      dsimp [Q]
      linarith [htri, hgrav, hcZ]
    change |-(2 * Z + μ) * s 1| ≤ max P Q ∧
      |(2 * Z - μ) * s 0| ≤ max P Q ∧
      |c * Z - (1 - μ) / 2 - μ * Z / d| ≤ max P Q
    exact ⟨hA.trans (le_max_left P Q), hB.trans (le_max_left P Q),
      hK.trans (le_max_right P Q)⟩
  obtain ⟨M, hM, hcoeff⟩ := hcoeff
  refine ⟨4 * M + 4, ?_⟩
  intro s hx hy hD henergy
  obtain ⟨hA, hB, hK⟩ := hcoeff s hx hy hD
  let A : ℝ := -(2 * zNormSq s + μ) * s 1
  let B : ℝ := (2 * zNormSq s - μ) * s 0
  let K : ℝ := c * zNormSq s - (1 - μ) / 2 -
    μ * zNormSq s / Real.sqrt (secondCollisionDistanceSq s)
  change |A| ≤ M at hA
  change |B| ≤ M at hB
  change |K| ≤ M at hK
  have heq : ((s 2) ^ 2 + (s 3) ^ 2) / 2 + A * s 2 + B * s 3 + K ≤ 0 := by
    unfold leviCivitaHamiltonian wNormSq at henergy
    dsimp [A, B, K]
    simp only [div_eq_mul_inv] at henergy ⊢
    linear_combination henergy
  have hAsq : A ^ 2 ≤ M ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg A) hM).mpr hA
    simpa only [sq_abs] using h
  have hBsq : B ^ 2 ≤ M ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg B) hM).mpr hB
    simpa only [sq_abs] using h
  have hsum : ((s 2) + A) ^ 2 + ((s 3) + B) ^ 2 ≤ 2 * M ^ 2 + 2 * M := by
    nlinarith only [heq, hAsq, hBsq, (abs_le.mp hK).1]
  have huSq : ((s 2) + A) ^ 2 ≤ (2 * M + 2) ^ 2 := by
    nlinarith only [hsum, sq_nonneg ((s 3) + B), sq_nonneg M, hM]
  have hvSq : ((s 3) + B) ^ 2 ≤ (2 * M + 2) ^ 2 := by
    nlinarith only [hsum, sq_nonneg ((s 2) + A), sq_nonneg M, hM]
  have hshiftu : |(s 2) + A| ≤ 2 * M + 2 :=
    abs_le_of_sq_le_sq huSq (by linarith)
  have hshiftv : |(s 3) + B| ≤ 2 * M + 2 :=
    abs_le_of_sq_le_sq hvSq (by linarith)
  constructor
  · calc
      |s 2| = |((s 2) + A) + (-A)| := by ring
      _ ≤ |(s 2) + A| + |-A| := abs_add_le _ _
      _ = |(s 2) + A| + |A| := by rw [abs_neg]
      _ ≤ 4 * M + 4 := by linarith
  · calc
      |s 3| = |((s 3) + B) + (-B)| := by ring
      _ ≤ |(s 3) + B| + |-B| := abs_add_le _ _
      _ = |(s 3) + B| + |B| := by rw [abs_neg]
      _ ≤ 4 * M + 4 := by linarith
