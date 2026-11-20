-- Prove2me | solution 2 for AvramDividend.Classical.avram_jump6_B_original_finitecap_integrable_discounted_localtime_mean_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T07:41:07.515211+00:00
-- url     : https://prove2.me/submissions/86ec4749-d29e-4e45-a3da-dd91c16cdca6

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB47_original_finitecap_discounted_kink_localtime_correction_nonpositive
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (S : Finset ℕ) (j : ℕ → ℕ)
    (L E : ℕ → Ω → ℝ)
    (hL : ∀ ω i, i ∈ S → 0 ≤ L i ω)
    (hE : ∀ ω i, i ∈ S → 0 ≤ E i ω)
    (hI : Integrable
      (fun ω => ∑ i ∈ S,
        E i ω * (((1 - deriv w (C.toReal * (((j i + 1 : ℕ) : ℝ) /
          ((j i + 2 : ℕ) : ℝ)))) / 2) * L i ω)) P) :
    (∫ ω, ∑ i ∈ S,
      E i ω * (((1 - deriv w (C.toReal * (((j i + 1 : ℕ) : ℝ) /
        ((j i + 2 : ℕ) : ℝ)))) / 2) * L i ω) ∂P) ≤ 0 := by
  apply integral_nonpos_of_ae
  filter_upwards [] with ω
  apply Finset.sum_nonpos
  intro i hi
  simpa only using
    (avram_gbB47_original_finitecap_discounted_kink_localtime_correction_nonpositive
      w C hC hFiniteCap hw_smooth hw_grad (j i)
      (L i ω) (E i ω) (hL ω i hi) (hE ω i hi))
