-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_canonical_discount_error_finite_and_vanishing
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T21:09:36.337593+00:00
-- url     : https://prove2.me/submissions/7920b837-654e-4a57-a7a9-f53d84ab766a

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : AvramDividend.Classical.IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) (q : ℝ) (hq : 0 ≤ q) :
    let E : ℕ → ℝ≥0∞ := fun j =>
      ENNReal.ofReal (q * ((1 : ℝ) / ((j : ℝ) + 1))) *
        AvramDividend.Classical.dividendMeasure D ω (Ioc (0 : ℝ) (t : ℝ))
    (∀ j, E j ≠ ⊤) ∧
    Tendsto (fun j => (E j).toReal) atTop (𝓝 (0 : ℝ)) := by
  intro E
  have hM : AvramDividend.Classical.dividendMeasure D ω (Ioc (0 : ℝ) (t : ℝ)) ≠ ⊤ := by
    unfold AvramDividend.Classical.dividendMeasure
    split_ifs with h
    · rw [StieltjesFunction.measure_Ioc]; exact ENNReal.ofReal_ne_top
    · simp
  refine ⟨fun j => ENNReal.mul_ne_top ENNReal.ofReal_ne_top hM, ?_⟩
  have hE : (fun j => (E j).toReal) = fun j : ℕ =>
      q * ((1 : ℝ) / ((j : ℝ) + 1)) *
        (AvramDividend.Classical.dividendMeasure D ω (Ioc (0 : ℝ) (t : ℝ))).toReal := by
    funext j
    simp only [E, ENNReal.toReal_mul]
    rw [ENNReal.toReal_ofReal (by positivity)]
  rw [hE]
  have h0 : Tendsto (fun j : ℕ => (1 : ℝ) / ((j : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have := (h0.const_mul q).mul_const
    (AvramDividend.Classical.dividendMeasure D ω (Ioc (0 : ℝ) (t : ℝ))).toReal
  simpa using this
