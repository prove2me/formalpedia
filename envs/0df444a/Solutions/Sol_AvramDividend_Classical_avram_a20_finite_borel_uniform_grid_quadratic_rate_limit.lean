-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_finite_borel_uniform_grid_quadratic_rate_limit
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-12T13:57:00.709339+00:00
-- url     : https://prove2.me/submissions/72eaccb0-ca19-40b5-9c0a-a3ca2c001284

import Mathlib

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

noncomputable section

set_option autoImplicit false

private lemma ofReal_rate_square (μ : Measure ℝ) (B : Set ℝ) (T : ℝ≥0) (hν : μ B < ⊤) :
    ENNReal.ofReal ((((T : ℝ) * (μ B).toReal) ^ 2) / 2) =
      (((T : ℝ≥0∞) * μ B) ^ 2) / 2 := by
  have hμ : μ B ≠ ⊤ := ne_of_lt hν
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ (T : ℝ) * (μ B).toReal)]
  rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (T : ℝ))]
  rw [ENNReal.ofReal_coe_nnreal]
  rw [ENNReal.ofReal_toReal hμ]
  rw [ENNReal.ofReal_ofNat]

/-- The uniform-grid quadratic rate converges to the square rate. -/
theorem solution (μ : Measure ℝ) (B : Set ℝ) (T : ℝ≥0) (hν : μ B < ⊤) :
    Tendsto
      (fun m : ℕ => ENNReal.ofReal
        (((m : ℝ) * ((m : ℝ) - 1) / 2) *
          (((T : ℝ) * (μ B).toReal) ^ 2 / (m : ℝ) ^ 2)))
      atTop (𝓝 ((((T : ℝ≥0∞) * μ B) ^ 2) / 2)) := by
  set A : ℝ := ((T : ℝ) * (μ B).toReal) ^ 2 with hA
  set L : ℝ := A / 2 with hL
  have hreal : Tendsto
      (fun m : ℕ => ((m : ℝ) * ((m : ℝ) - 1) / 2) * (A / (m : ℝ) ^ 2)) atTop (𝓝 L) := by
    have hinv : Tendsto (fun m : ℕ => ((m : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have h1 : Tendsto (fun m : ℕ => 1 - ((m : ℝ))⁻¹) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub hinv
    have h2 : Tendsto (fun m : ℕ => L * (1 - ((m : ℝ))⁻¹)) atTop (𝓝 (L * (1 - 0))) :=
      h1.const_mul L
    have h2' : Tendsto (fun m : ℕ => L * (1 - ((m : ℝ))⁻¹)) atTop (𝓝 L) := by
      simpa using h2
    refine h2'.congr' ?_
    apply eventually_atTop.mpr
    refine ⟨1, ?_⟩
    intro m hm
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
    simp only [hL]
    field_simp
  have hcomp : Tendsto
      (fun m : ℕ => ENNReal.ofReal
        (((m : ℝ) * ((m : ℝ) - 1) / 2) * (A / (m : ℝ) ^ 2)))
      atTop (𝓝 (ENNReal.ofReal L)) :=
    (ENNReal.continuous_ofReal.tendsto L).comp hreal
  have hof : ENNReal.ofReal L = (((T : ℝ≥0∞) * μ B) ^ 2) / 2 := by
    rw [hL, hA]
    exact ofReal_rate_square μ B T hν
  rwa [hof] at hcomp
