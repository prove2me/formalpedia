-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_original_strict_cash_uniform_grid_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T01:01:08.609589+00:00
-- url     : https://prove2.me/submissions/56322859-678c-4c76-b4ac-f6bb0965098e

import Theorems.Thm_AvramDividend_Classical_avram_chat24_original_strict_cash_grid_limit_of_discount_modulus
import Theorems.Thm_AvramDividend_Classical_avram_chat24_nonnegative_discount_cell_modulus
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (B : ℝ≥0) :
    Tendsto (fun n : ℕ =>
      let N : ℕ := n + 1
      let u : ℕ → ℝ≥0 := fun i => B * (i : ℝ≥0) / (N : ℝ≥0)
      ∑ i ∈ Finset.range N, Real.exp (-(q * (u i : ℝ))) *
        (D (u (i + 1)) ω - D (u i) ω)) atTop
      (nhds ((∫⁻ t in Ico (0 : ℝ) (B : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal)) := by
  let u : ℕ → ℕ → ℝ≥0 := fun n i => B * (i : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)
  have hu (n : ℕ) : Monotone (u n) := by
    intro i j hij
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hij) (show 0 ≤ B from by positivity))
      (show 0 ≤ ((n + 1 : ℕ) : ℝ≥0) from by positivity)
  have hu0 (n : ℕ) : u n 0 = 0 := by simp [u]
  have huN (n : ℕ) : u n (n + 1) = B := mul_div_cancel_right₀ B (by positivity)
  have hmesh : Tendsto (fun n : ℕ => (B : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop (nhds 0) := by
    simpa only [Nat.cast_add, Nat.cast_one, mul_one_div, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (B : ℝ)
  apply avram_chat24_original_strict_cash_grid_limit_of_discount_modulus D hD ω q hq B
    u (fun n => n + 1) _ hu hu0 huN hmesh
  intro n i hi
  apply avram_chat24_nonnegative_discount_cell_modulus q _ _ _ hq (u n i).coe_nonneg
    (by exact_mod_cast hu n (Nat.le_succ i))
  dsimp [u]
  push_cast
  exact le_of_eq (by ring)
