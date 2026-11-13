-- Prove2me | solution 1 for CountingLLL.RandomRAM.source_accuracy_exact_sample_count
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T05:28:42.362267+00:00
-- url     : https://prove2.me/submissions/59e0e2cf-9cc5-4071-9815-db1d81e69127

import Theorems.Thm_CountingLLL_RandomRAM_source_moment_to_counting_accuracy

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

/-- The sample count chosen in #442 §5.3 is positive and satisfies the bound used for (34). -/
private theorem sample_count_properties (m : ℕ) (D ε : ℝ) (hm : 0 < m) (hD : 1 ≤ D) (he : 0 < ε) :
    let L : ℝ := (⌈8 * (m : ℝ) / ((D + 1)^2 * ε^2)⌉₊ : ℝ)
    0 < L ∧ 8 * (m : ℝ) ≤ L * (D + 1)^2 * ε^2 := by
  dsimp
  have hden : 0 < (D + 1)^2 * ε^2 := mul_pos (sq_pos_of_pos (by linarith)) (sq_pos_of_pos he)
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hpos : 0 < 8 * (m : ℝ) / ((D + 1)^2 * ε^2) := div_pos (by positivity) hden
  constructor
  · exact_mod_cast (Nat.ceil_pos.mpr hpos)
  · have h := (div_le_iff₀ hden).1 (Nat.le_ceil (8 * (m : ℝ) / ((D + 1)^2 * ε^2)))
    nlinarith

theorem solution {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ι → Ω → ℝ) (r : ι → ℝ)
    (a p D ε : ℝ) (L : ℕ)
    (hm : 0 < Fintype.card ι)
    (hLspec : L = ⌈8 * (Fintype.card ι : ℝ) / ((D + 1)^2 * ε^2)⌉₊)
    (ha : 0 < a) (hp : 0 ≤ p) (hD : 1 ≤ D) (he : 0 < ε) (he1 : ε ≤ 1)
    (hcondition : 4 * Real.exp 1 * p * (D + 1) ^ 2 ≤ 1)
    (hr0 : ∀ i, 0 ≤ r i) (hr : ∀ i, r i ≤ (6 / 5) * p)
    (hind : iIndepFun X μ) (hL2 : ∀ i, MemLp (X i) 2 μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = 1 - r i)
    (hvar : ∀ i, variance (X i) μ ≤ 3 * p / (L : ℝ))
    (f g : Ω → ℝ≥0∞) (Bf Bg : ℝ≥0∞)
    (hBf0 : Bf ≠ 0) (hBg0 : Bg ≠ 0) (hBft : Bf ≠ ⊤) (hBgt : Bg ≠ ⊤)
    (hf : Measurable f) (hg : Measurable g)
    (hEf : ∫⁻ ω, f ω ∂μ ≤ Bf) (hEg : ∫⁻ ω, g ω ∂μ ≤ Bg) :
    (13 / 16 : ℝ≥0∞) ≤ μ {ω |
      ((1 - ε) * (a * (∏ i, (1 - r i))) ≤ a * (∏ i, X i ω) ∧
      a * (∏ i, X i ω) ≤ (1 + ε) * (a * (∏ i, (1 - r i)))) ∧
      f ω < 16 * Bf ∧ g ω < 16 * Bg} := by
  have hprops := sample_count_properties (Fintype.card ι) D ε hm hD he
  rw [← hLspec] at hprops
  exact CountingLLL.RandomRAM.source_moment_to_counting_accuracy μ X r a p D (L : ℝ) ε
    ha hp hD hprops.1 he he1 hcondition hr0 hr hind hL2 hmean hvar hprops.2
    f g Bf Bg hBf0 hBg0 hBft hBgt hf hg hEf hEg
