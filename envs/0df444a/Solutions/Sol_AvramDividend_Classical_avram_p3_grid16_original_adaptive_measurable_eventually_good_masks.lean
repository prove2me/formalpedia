-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid16_original_adaptive_measurable_eventually_good_masks
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T18:57:15.626021+00:00
-- url     : https://prove2.me/submissions/9066bf6a-73a9-41b2-ab36-2793db31f282

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid15_original_adaptive_band_exception_finite_ae
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_finite_clock_predictable_left_reserve_jointly_measurable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Source-exact measurable eventual compact masks for every original physical grid row. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (a b : ℕ → ℝ)
    (hExh : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ k ≥ N, y ∈ Icc (a k) (b k))
    (u : ℕ → ℕ → ℝ≥0)
    (ε : ℕ → ℝ≥0∞) (hε : ∀ n, 0 < ε n)
    (hεsum : (∑' n, ε n) < ⊤) :
    ∃ κ : ℕ → ℕ, ∃ s : ℕ → Set Ω,
      (∀ n, n ≤ κ n) ∧
      (∀ n, s n = {ω : Ω | ∀ i < n + 1,
        (0 < Function.leftLim
          (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i) ∧
          ENNReal.ofReal (Function.leftLim
            (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)) < C) →
        Function.leftLim
          (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i) ∈
          Icc (a (κ n)) (b (κ n))}) ∧
      (∀ n, MeasurableSet (s n)) ∧
      (∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ s n) := by
  classical
  obtain ⟨κ, hκ, hfinite⟩ :=
    avram_p3_grid15_original_adaptive_band_exception_finite_ae
      X x D hD C a b hExh u ε hε hεsum
  let Z : ℕ → ℕ → Ω → ℝ := fun n i ω =>
    Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
  have hZ (n i : ℕ) : Measurable (Z n i) := by
    have hjoint :=
      avram_wave7_17_original_finite_clock_predictable_left_reserve_jointly_measurable
        X x D hD (u n i)
    have hfix : Measurable (fun ω : Ω => ((u n i), ω)) :=
      measurable_const.prodMk measurable_id
    have hcomp := hjoint.comp hfix
    convert hcomp using 1
    funext ω
    simp [Z]
  let s : ℕ → Set Ω := fun n =>
    {ω : Ω | ∀ i < n + 1,
      (0 < Z n i ω ∧ ENNReal.ofReal (Z n i ω) < C) →
        Z n i ω ∈ Icc (a (κ n)) (b (κ n))}
  have hsm (n : ℕ) : MeasurableSet (s n) := by
    dsimp [s]
    measurability
  have hfin : ∀ᵐ ω ∂P, ({n : ℕ | ω ∈ (s n)ᶜ}).Finite := by
    simpa only [s, Z] using hfinite
  refine ⟨κ, s, hκ, ?_, hsm, ?_⟩
  · intro n
    rfl
  · filter_upwards [hfin] with ω hω
    obtain ⟨N, hN⟩ := hω.bddAbove
    filter_upwards [Filter.eventually_ge_atTop (N + 1)] with n hn
    by_contra hbad
    have hnBad : n ∈ {n : ℕ | ω ∈ (s n)ᶜ} := hbad
    have hnLe : n ≤ N := hN hnBad
    omega
