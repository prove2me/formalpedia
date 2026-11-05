-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_original_negative_compact_mean_measure_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:09:46.385189+00:00
-- url     : https://prove2.me/submissions/57d47a34-d03b-4bca-a32d-4c4808aa5c9e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_assist_public_original_mark_marginal_tonelli
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_finite_compact_test_mark_lintegral
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_compact_negative_test_vanishes_near_zero
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_nonnegative_compact_jump_lintegral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Tonelli for the actual original source finite compact jump sum. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ρ : Measure ℝ)
    (hρ : ∀ B : Set ℝ, MeasurableSet B →
      ρ B = (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (1 : ℝ≥0) ×ˢ B) ∂P))
    (g : ℝ → ℝ) (hg : Continuous g)
    (hc : IsCompact (tsupport g))
    (hneg : tsupport g ⊆ Iio (0 : ℝ))
    (hgnonneg : ∀ y : ℝ, 0 ≤ g y) :
    (∫⁻ y, ENNReal.ofReal (g y) ∂ρ) =
      ENNReal.ofReal (∫ y : ℝ, g y ∂(X.ν.restrict (Iio (0 : ℝ)))) := by
  classical
  let C : Set (ℝ≥0 × ℝ) := Ioc 0 (1 : ℝ≥0) ×ˢ (Set.univ : Set ℝ)
  have hC : MeasurableSet C := measurableSet_Ioc.prod MeasurableSet.univ
  let NX (ω : Ω) : Measure (ℝ≥0 × ℝ) :=
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  have hgm : Measurable (fun y : ℝ => ENNReal.ofReal (g y)) :=
    ENNReal.measurable_ofReal.comp hg.measurable
  obtain ⟨ρ₀, hρ₀, hlin⟩ :=
    avram_p2_a_assist_public_original_mark_marginal_tonelli
      X (1 : ℝ≥0) (fun y => ENNReal.ofReal (g y)) hgm
  have hρeq : ρ₀ = ρ := by
    apply Measure.ext
    intro B hB
    exact (hρ₀ B hB).trans (hρ B hB).symm
  obtain ⟨J, _, hJsum, _, hJmean⟩ :=
    avram_p2_a_zero_rate_original_nonnegative_compact_jump_lintegral
      P X (1 : ℝ≥0) (by norm_num) g hg hc hneg hgnonneg
  obtain ⟨ε, hε, hvanish⟩ :=
    avram_p2_a_zero_rate_compact_negative_test_vanishes_near_zero
      g hg hc hneg
  have hv : ∀ y : ℝ, dist y 0 < ε → g y = 0 := by
    intro y hy
    exact hvanish y (by simpa [Real.dist_eq] using hy)
  have hpath (ω : Ω) :
      (∫⁻ p in C, ENNReal.ofReal (g p.2) ∂(NX ω)) =
        ENNReal.ofReal (J ω) := by
    obtain ⟨F, hF, hFint⟩ :=
      avram_p2_a_zero_rate_original_finite_compact_test_mark_lintegral
        X ω (1 : ℝ≥0) g hg ε hε hv
    obtain ⟨F', hF', hJfin⟩ := hJsum ω
    have hFF' : F = F' := Finset.ext (fun u => (hF u).trans (hF' u).symm)
    rw [hFF'] at hFint
    have hnonneg (u : ℝ≥0) : 0 ≤
        g (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) :=
      hgnonneg _
    calc
      (∫⁻ p in C, ENNReal.ofReal (g p.2) ∂(NX ω)) =
          (∫⁻ p, C.indicator (fun p => ENNReal.ofReal (g p.2)) p ∂(NX ω)) :=
        (lintegral_indicator hC (fun p => ENNReal.ofReal (g p.2))).symm
      _ = (∫⁻ p,
          (if p.1 ∈ Ioc (0 : ℝ≥0) (1 : ℝ≥0)
            then ENNReal.ofReal (g p.2) else 0) ∂(NX ω)) := by
        congr 1
        funext p
        simp [C, Set.indicator]
      _ = ∑ u ∈ F', ENNReal.ofReal
          (g (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) :=
        hFint
      _ = ENNReal.ofReal (∑ u ∈ F',
          g (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) := by
        exact (ENNReal.ofReal_sum_of_nonneg
          (by intro u hu; exact hnonneg u)).symm
      _ = ENNReal.ofReal (J ω) := by rw [hJfin]
  calc
    (∫⁻ y, ENNReal.ofReal (g y) ∂ρ) =
        (∫⁻ ω, ∫⁻ p in C, ENNReal.ofReal (g p.2) ∂(NX ω) ∂P) := by
      rw [← hρeq]
      simpa only [NX, C] using hlin
    _ = (∫⁻ ω, ENNReal.ofReal (J ω) ∂P) :=
      lintegral_congr_ae (Filter.Eventually.of_forall hpath)
    _ = _ := by simpa using hJmean
