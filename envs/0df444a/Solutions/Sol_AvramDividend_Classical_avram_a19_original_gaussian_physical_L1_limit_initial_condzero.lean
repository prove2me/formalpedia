-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_original_gaussian_physical_L1_limit_initial_condzero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T00:17:53.865334+00:00
-- url     : https://prove2.me/submissions/6bebbb79-b0cd-4746-b5f0-a15f15f1e478

import Mathlib
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_stop_original_cells_F0_centred
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_initial_condexp_zero_of_L1_limit
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

/-- The true stopped Gaussian physical grid limit inherits initial conditional centring. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (hF0 : 𝓕.rightCont 0 ≤ mΩ)
    (S : ℕ → Finset ι) (τ : ℕ → ι → Ω → ℝ≥0)
    (hτ : ∀ n, ∀ i ∈ S n, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ n i ω ≤ s})
    (B : ℕ → ι → ℝ≥0)
    (hBound : ∀ n, ∀ i ∈ S n, ∀ ω, τ n i ω ≤ B n i)
    (h : ℕ → ι → ℝ≥0) (G H : ℕ → ι → Ω → ℝ)
    (hG : ∀ n i (hi : i ∈ S n),
      Measurable[(isStoppingTime_withTop_of_le_events
        (τ n i) (hτ n i hi)).measurableSpace] (G n i))
    (hH : ∀ n i (hi : i ∈ S n),
      Measurable[(isStoppingTime_withTop_of_le_events
        (τ n i) (hτ n i hi)).measurableSpace] (H n i))
    (M : ℕ → ι → Ω → ℝ)
    (hM : ∀ n, M n = fun i ω =>
      (X.X (τ n i ω + h n i) ω -
        ((τ n i ω + h n i) : ℝ) * X.c) -
      (X.X (τ n i ω) ω - (τ n i ω : ℝ) * X.c))
    (hGI : ∀ n, ∀ i ∈ S n,
      Integrable (fun ω => G n i ω * M n i ω) P)
    (hHI : ∀ n, ∀ i ∈ S n, Integrable (H n i) P)
    (hH2I : ∀ n, ∀ i ∈ S n,
      Integrable (fun ω => H n i ω * (M n i ω) ^ 2) P)
    (L : Ω → ℝ) (hLI : Integrable L P)
    (hL1 : Tendsto
      (fun n => eLpNorm (fun ω =>
        L ω - ∑ i ∈ S n,
          (G n i ω * M n i ω +
            (H n i ω * M n i ω ^ 2 -
              ((h n i : ℝ) * X.σ ^ 2) * H n i ω))) 1 P)
      atTop (nhds 0)) :
    condExp (𝓕.rightCont 0) P L =ᵐ[P] (fun _ => (0 : ℝ))  := by
  let Q : ℕ → Ω → ℝ := fun n ω =>
    ∑ i ∈ S n,
      (G n i ω * M n i ω +
        (H n i ω * M n i ω ^ 2 -
          ((h n i : ℝ) * X.σ ^ 2) * H n i ω))
  have hLocal (n : ℕ) :
      Integrable (Q n) P ∧
      condExp (𝓕.rightCont 0) P (Q n) =ᵐ[P]
        (fun _ => (0 : ℝ)) := by
    simpa only [Q] using
      (avram_ubv_gauss13_stop_original_cells_F0_centred
        X hν (S n) (τ n) (hτ n) (B n)
        (hBound n) (h n) (G n) (H n)
        (hG n) (hH n) (M n) (hM n)
        (hGI n) (hHI n) (hH2I n))
  have hIntQ : ∀ n, Integrable (Q n) P :=
    fun n => (hLocal n).1
  have hZeroQ : ∀ n,
      condExp (𝓕.rightCont 0) P (Q n) =ᵐ[P]
        (fun _ => (0 : ℝ)) :=
    fun n => (hLocal n).2
  change Tendsto
    (fun n => eLpNorm (fun ω => L ω - Q n ω) 1 P)
    atTop (nhds 0) at hL1
  exact avram_jump6_A_initial_condexp_zero_of_L1_limit
    (𝓕.rightCont 0) hF0 Q L
    hIntQ hLI hZeroQ hL1
