-- Prove2me | solution 1 for BirkhoffGlobalSection.regular_energy_coefficients_bounded_on_box
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T08:34:44.947917+00:00
-- url     : https://prove2.me/submissions/8799d483-a7f3-4223-aa3e-680522743e6c

import Mathlib
import Definitions.Def_BirkhoffGlobalSection

open BirkhoffGlobalSection

theorem solution (μ c Rz δ : ℝ) (hδ : 0 < δ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s ∈ regularEnergyLocus μ c,
      |s 0| ≤ Rz → |s 1| ≤ Rz →
      δ ≤ Real.sqrt (secondCollisionDistanceSq s) →
      |-(2 * zNormSq s + μ) * s 1| ≤ M ∧
      |(2 * zNormSq s - μ) * s 0| ≤ M ∧
      |c * zNormSq s - (1 - μ) / 2 -
        μ * zNormSq s / Real.sqrt (secondCollisionDistanceSq s)| ≤ M := by
  let R : ℝ := |Rz| + 1
  let T : ℝ := 2 * R ^ 2
  let P : ℝ := (2 * T + |μ|) * R
  let Q : ℝ := |c| * T + (1 + |μ|) / 2 + |μ| * T / δ
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  refine ⟨max P Q, le_max_of_le_left hP, ?_⟩
  intro s hs hx hy hd
  let Z : ℝ := zNormSq s
  let d : ℝ := Real.sqrt (secondCollisionDistanceSq s)
  have hdpos : 0 < d := lt_of_lt_of_le hδ hd
  have hZnonneg : 0 ≤ Z := by dsimp [Z, zNormSq]; positivity
  have hxR : |s 0| ≤ R := by dsimp [R]; linarith [le_abs_self Rz]
  have hyR : |s 1| ≤ R := by dsimp [R]; linarith [le_abs_self Rz]
  have hxSq : (s 0) ^ 2 ≤ R ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg (s 0)) hR).mpr hxR
    simpa only [sq_abs] using h
  have hySq : (s 1) ^ 2 ≤ R ^ 2 := by
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
  have hgrav : |μ| * Z / d ≤ |μ| * T / δ := by
    apply (div_le_div_iff₀ hdpos hδ).2
    calc
      |μ| * Z * δ ≤ |μ| * T * δ :=
        mul_le_mul_of_nonneg_right hnum (le_of_lt hδ)
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
