-- Prove2me | solution 1 for AvramDividend.Classical.avram_gfinite63_unit_occupation_integral_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T23:52:21.865132+00:00
-- url     : https://prove2.me/submissions/5c3c9344-2218-45ea-989a-7950c3b47489

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section

theorem solution (n : ℕ) (f : ℝ → ℝ)
    (hfInt : IntegrableOn f (Ioo (0 : ℝ) (n : ℝ)) volume)
    (hf0 : ∀ t, 0 ≤ f t) (hf1 : ∀ t, f t ≤ 1) :
    0 ≤ (∫ t in Ioo (0 : ℝ) (n : ℝ), f t ∂volume) ∧
      (∫ t in Ioo (0 : ℝ) (n : ℝ), f t ∂volume) ≤ (n : ℝ) := by
  have hlow :
      0 ≤ ∫ t in Ioo (0 : ℝ) (n : ℝ), f t ∂volume := by
    apply MeasureTheory.integral_nonneg
    intro t
    exact hf0 t
  have hhigh :
      (∫ t in Ioo (0 : ℝ) (n : ℝ), f t ∂volume) ≤
      (∫ t in Ioo (0 : ℝ) (n : ℝ), (1 : ℝ) ∂volume) := by
    have hFinite : volume (Ioo (0 : ℝ) (n : ℝ)) ≠ ⊤ := by
      simp
    have hOneInt : IntegrableOn (fun _ : ℝ => (1 : ℝ))
        (Ioo (0 : ℝ) (n : ℝ)) volume :=
      integrableOn_const hFinite
    apply MeasureTheory.integral_mono hfInt hOneInt
    exact hf1
  have hone :
      (∫ t in Ioo (0 : ℝ) (n : ℝ), (1 : ℝ) ∂volume) =
        (n : ℝ) := by
    simp
  exact ⟨hlow, hhigh.trans (le_of_eq hone)⟩
