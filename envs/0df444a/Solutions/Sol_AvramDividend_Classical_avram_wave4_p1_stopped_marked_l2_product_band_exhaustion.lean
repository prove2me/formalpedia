-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_stopped_marked_l2_product_band_exhaustion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T22:22:49.005436+00:00
-- url     : https://prove2.me/submissions/0ffeb396-3250-4aab-86ba-dc27f1f72097

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_levy_square_energy_band_tails
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_marked_product_square_kernel_integrable_of_domination

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem solution
    {A E : Type*} [MeasurableSpace A] [MeasurableSpace E]
    (μ : Measure A) [IsFiniteMeasure μ]
    (ν : Measure E) [SFinite ν]
    (g : E → ℝ≥0∞) (hg : Measurable g)
    (henergy : ∫⁻ z, g z ∂ν < ∞)
    (F : A × E → ℝ≥0∞) (hF : Measurable F)
    (C : ℝ≥0∞) (hC : C < ∞)
    (hdom : ∀ p, F p ≤ C * g p.2)
    (B : ℕ → Set E) (hB : ∀ n, MeasurableSet (B n))
    (hBfinite : ∀ n, ν (B n) < ∞)
    (hBmono : Monotone B)
    (hBcover : (⋃ n, B n) = Set.univ) :
    Tendsto (fun n : ℕ =>
      ∫⁻ p in Set.univ ×ˢ (B n)ᶜ, F p ∂μ.prod ν)
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by
  have hFfinite : (∫⁻ p, F p ∂μ.prod ν) < ∞ :=
    AvramDividend.Classical.avram_wave4_p1_marked_product_square_kernel_integrable_of_domination
      μ ν g hg henergy F C hC hdom
  let B' : ℕ → Set (A × E) := fun n => Set.univ ×ˢ B n
  have hB'meas (n : ℕ) : MeasurableSet (B' n) := by
    exact MeasurableSet.univ.prod (hB n)
  have hB'finite (n : ℕ) : (μ.prod ν) (B' n) < ∞ := by
    rw [show B' n = Set.univ ×ˢ B n by rfl, Measure.prod_prod]
    exact ENNReal.mul_lt_top (measure_lt_top μ Set.univ) (hBfinite n)
  have hB'mono : Monotone B' := by
    intro i j hij p hp
    exact ⟨hp.1, hBmono hij hp.2⟩
  have hB'cover : (⋃ n, B' n) = Set.univ := by
    ext p
    constructor
    · intro _; trivial
    · intro _
      have hp : p.2 ∈ ⋃ n, B n := by simp [hBcover]
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hp
      exact Set.mem_iUnion.mpr ⟨n, ⟨Set.mem_univ _, hn⟩⟩
  have htail :=
    AvramDividend.Classical.avram_wave4_p1_levy_square_energy_band_tails
      (μ.prod ν) F hF hFfinite B' hB'meas hB'finite hB'mono hB'cover
  have hcomp (n : ℕ) : (B' n)ᶜ = Set.univ ×ˢ (B n)ᶜ := by
    ext p
    simp [B', Set.mem_prod]
  simpa only [hcomp] using htail
