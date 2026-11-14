-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB289_original_dividend_fourth_power_mesh_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:09:46.683204+00:00
-- url     : https://prove2.me/submissions/4c02ba7b-c5c8-41fa-b457-36ef66dac543

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

/-- Original adapted monotone dividends remain monotone on a fourth-power mesh with exact endpoint. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (n m : ℕ) (hm : 0 < m) :
    Monotone (fun i : ℕ =>
      D ((i : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) ω) ∧
    D (((n * m ^ 4 : ℕ) : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) ω = D n ω ∧
    D ((0 : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) ω = D 0 ω := by
  have hmpos : (0 : ℝ≥0) < m := by exact_mod_cast hm
  have hmne : (m : ℝ≥0) ≠ 0 := ne_of_gt hmpos
  have hp : (m : ℝ≥0) ^ 4 ≠ 0 := pow_ne_zero 4 hmne
  have hcancel : (m : ℝ≥0) ^ 4 * (1 / ((m : ℝ≥0) ^ 4)) = 1 := by
    simpa [one_div] using (mul_inv_cancel₀ hp)
  have heq : (((n * m ^ 4 : ℕ) : ℝ≥0) *
      (1 / ((m : ℝ≥0) ^ 4))) = (n : ℝ≥0) := by
    calc
      _ = (n : ℝ≥0) * ((m : ℝ≥0) ^ 4 *
          (1 / ((m : ℝ≥0) ^ 4))) := by
            push_cast
            ring
      _ = (n : ℝ≥0) := by rw [hcancel, mul_one]
  refine ⟨?_, ?_, by simp⟩
  · intro i j hij
    apply (hD.2.1 ω)
    apply mul_le_mul_of_nonneg_right
    · exact_mod_cast hij
    · positivity
  · rw [heq]
