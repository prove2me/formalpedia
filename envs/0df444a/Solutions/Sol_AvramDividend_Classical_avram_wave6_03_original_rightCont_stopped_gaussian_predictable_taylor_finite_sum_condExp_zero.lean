-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_gaussian_predictable_taylor_finite_sum_condExp_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T08:47:53.622491+00:00
-- url     : https://prove2.me/submissions/a03b16b6-7313-49b6-899e-fc9f842f8f0d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_predictable_taylor_residual_condExp_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (S : Finset ι)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (B : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ B)
    (h : ι → ℝ≥0) (G H : ι → Ω → ℝ)
    (hG : ∀ i ∈ S,
      Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] (G i))
    (hH : ∀ i ∈ S,
      Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] (H i))
    (hGI : ∀ i ∈ S, Integrable (fun ω =>
      G i ω * (X.X (τ ω + h i) ω - X.X (τ ω) ω - (h i : ℝ) * X.c)) P)
    (hHI : ∀ i ∈ S, Integrable (H i) P)
    (hH2I : ∀ i ∈ S, Integrable (fun ω =>
      H i ω * (X.X (τ ω + h i) ω - X.X (τ ω) ω - (h i : ℝ) * X.c) ^ 2) P) :
    let Y : ι → Ω → ℝ := fun i ω =>
      X.X (τ ω + h i) ω - X.X (τ ω) ω - (h i : ℝ) * X.c
    let F : ι → Ω → ℝ := fun i ω =>
      G i ω * Y i ω +
        (H i ω * Y i ω ^ 2 - ((h i : ℝ) * X.σ ^ 2) * H i ω)
    Integrable (fun ω => ∑ i ∈ S, F i ω) P ∧
      P[(fun ω => ∑ i ∈ S, F i ω) |
          (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
        =ᵐ[P] (fun _ => (0 : ℝ)) := by
  classical
  dsimp only
  let Y : ι → Ω → ℝ := fun i ω =>
    X.X (τ ω + h i) ω - X.X (τ ω) ω - (h i : ℝ) * X.c
  let F : ι → Ω → ℝ := fun i ω =>
    G i ω * Y i ω +
      (H i ω * Y i ω ^ 2 - ((h i : ℝ) * X.σ ^ 2) * H i ω)
  have hcell (i : ι) (hi : i ∈ S) :
      Integrable (F i) P ∧
        P[F i | (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] =ᵐ[P] (fun _ => (0 : ℝ)) := by
    have hs :=
      avram_wave6_03_original_rightCont_stopped_gaussian_predictable_taylor_residual_condExp_zero
        X hν τ hτ B hbounded (h i) (G i) (H i)
        (hG i hi) (hH i hi) (hGI i hi) (hHI i hi) (hH2I i hi)
    dsimp only at hs
    change Integrable (F i) P ∧
      P[F i | (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] =ᵐ[P] (fun _ => (0 : ℝ)) at hs
    exact hs
  have hfinite : ∀ T : Finset ι, T ⊆ S →
      Integrable (fun ω => ∑ i ∈ T, F i ω) P ∧
        P[(fun ω => ∑ i ∈ T, F i ω) | (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
          =ᵐ[P] (fun _ => (0 : ℝ)) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
        intro _
        constructor
        · simpa using (integrable_zero Ω ℝ P)
        · simp
    | @insert i T hnot ih =>
        intro hsub
        have hiS : i ∈ S := hsub (Finset.mem_insert_self i T)
        have hTS : T ⊆ S := by
          intro j hj
          exact hsub (Finset.mem_insert_of_mem hj)
        obtain ⟨hiI, hiZ⟩ := hcell i hiS
        obtain ⟨hTI, hTZ⟩ := ih hTS
        have heq :
            (fun ω => ∑ j ∈ insert i T, F j ω) =
              F i + (fun ω => ∑ j ∈ T, F j ω) := by
          funext ω
          exact Finset.sum_insert hnot
        rw [heq]
        constructor
        · exact hiI.add hTI
        · calc
            P[F i + (fun ω => ∑ j ∈ T, F j ω) | (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
                =ᵐ[P]
              P[F i | (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] +
                P[(fun ω => ∑ j ∈ T, F j ω) | (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] :=
              condExp_add hiI hTI _
            _ =ᵐ[P] (fun _ => (0 : ℝ)) := by
              filter_upwards [hiZ, hTZ] with ω ha hr
              exact (congrArg₂ (· + ·) ha hr).trans (zero_add 0)
  exact hfinite S (Finset.Subset.rfl)
