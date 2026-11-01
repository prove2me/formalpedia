-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_signed_l1_stopped_marked_band_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T00:10:51.516673+00:00
-- url     : https://prove2.me/submissions/315ba020-efed-49c8-8a2d-95f2d0b59abb

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_levy_square_energy_band_tails

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem solution
    {A E : Type*} [MeasurableSpace A] [MeasurableSpace E]
    (μ : Measure A) [IsFiniteMeasure μ]
    (ν : Measure E) [SFinite ν]
    (F : A × E → ℝ) (hFm : Measurable F)
    (hFi : Integrable F (μ.prod ν))
    (B : ℕ → Set E) (hB : ∀ n, MeasurableSet (B n))
    (hBfinite : ∀ n, ν (B n) < ∞)
    (hBmono : Monotone B)
    (hBcover : (⋃ n, B n) = Set.univ) :
    Tendsto (fun n : ℕ =>
      ∫⁻ p in Set.univ ×ˢ (B n)ᶜ, ‖F p‖ₑ ∂μ.prod ν)
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by
  have hFfinite : (∫⁻ p, ‖F p‖ₑ ∂μ.prod ν) < ∞ :=
    hFi.hasFiniteIntegral
  let B' : ℕ → Set (A × E) := fun n => Set.univ ×ˢ B n
  have hB'meas (n : ℕ) : MeasurableSet (B' n) :=
    MeasurableSet.univ.prod (hB n)
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
      (μ.prod ν) (fun p => ‖F p‖ₑ)
      (measurable_enorm.comp hFm) hFfinite
      B' hB'meas hB'finite hB'mono hB'cover
  have hcomp (n : ℕ) : (B' n)ᶜ = Set.univ ×ˢ (B n)ᶜ := by
    ext p
    simp [B', Set.mem_prod]
  simpa only [hcomp] using htail
