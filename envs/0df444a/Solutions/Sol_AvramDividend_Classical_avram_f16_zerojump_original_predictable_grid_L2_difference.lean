-- Prove2me | solution 1 for AvramDividend.Classical.avram_f16_zerojump_original_predictable_grid_L2_difference
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T00:07:46.826233+00:00
-- url     : https://prove2.me/submissions/8faca06d-d11a-4d6e-b60f-e0237ea340f7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ae_original_predictable_simple_integral_difference_L2
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*} [DecidableEq ι]
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (S : Finset ι) (s t : ι → ℝ≥0) (G H : ι → Ω → ℝ)
    (hst : ∀ i ∈ S, s i ≤ t i)
    (hSep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      t i ≤ s j ∨ t j ≤ s i)
    (hGown : ∀ i ∈ S, Measurable[𝓕.rightCont (s i)] (G i))
    (hHown : ∀ i ∈ S, Measurable[𝓕.rightCont (s i)] (H i))
    (hGpair : ∀ i ∈ S, ∀ j ∈ S, t i ≤ s j →
      Measurable[𝓕.rightCont (s j)] (G i))
    (hHpair : ∀ i ∈ S, ∀ j ∈ S, t i ≤ s j →
      Measurable[𝓕.rightCont (s j)] (H i))
    (hLp : ∀ i ∈ S, MemLp (fun ω =>
      (G i ω - H i ω) *
        ((X.X (t i) ω - (t i : ℝ) * X.c) -
         (X.X (s i) ω - (s i : ℝ) * X.c))) 2 P) :
    let V : ι → Ω → ℝ := fun i ω =>
      (X.X (t i) ω - (t i : ℝ) * X.c) -
      (X.X (s i) ω - (s i : ℝ) * X.c)
    let SG : Ω → ℝ := fun ω => ∑ i ∈ S, G i ω * V i ω
    let SH : Ω → ℝ := fun ω => ∑ i ∈ S, H i ω * V i ω
    MemLp (fun ω => SG ω - SH ω) 2 P ∧
    Integrable (fun ω => (SG ω - SH ω) ^ 2) P ∧
    (∫ ω, (SG ω - SH ω) ^ 2 ∂P) =
      ∑ i ∈ S, (∫ ω, ((G i ω - H i ω) * V i ω) ^ 2 ∂P) := by
  classical
  have hSource : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      X.X u ω = (u : ℝ) * X.c +
        (X.X u ω - (u : ℝ) * X.c) + 0 + 0 := by
    filter_upwards [] with ω
    intro u
    ring
  have hLp' : ∀ i ∈ S, MemLp (fun ω =>
      (G i ω - H i ω) *
        ((X.X (t i) ω - (t i : ℝ) * X.c - (0 : ℝ) - 0) -
         (X.X (s i) ω - (s i : ℝ) * X.c - (0 : ℝ) - 0))) 2 P := by
    intro i hi
    simpa only [sub_zero] using hLp i hi
  simpa only [sub_zero] using
    (avram_p4_a_gaussian_ae_original_predictable_simple_integral_difference_L2
      X X hν rfl (fun _ _ => 0) (fun _ _ => 0) hSource
      S s t G H hst hSep hGown hHown hGpair hHpair hLp')
