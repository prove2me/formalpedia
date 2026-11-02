-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_03_original_rightCont_gaussian_past_cross_increment_condExp_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T23:50:37.328502+00:00
-- url     : https://prove2.me/submissions/a98e2cbb-7a1d-4921-8378-c83b095650a7

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stoppedSigma_indep_shifted_source
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_gaussian_deterministic_increment_condExp_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The genuine past source Gaussian centred state times its future original
centred increment is L1 and conditionally centred, including sigma zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (s t : ℝ≥0) (hst : s ≤ t) :
    let Ms : Ω → ℝ := fun ω => X.X s ω - (s : ℝ) * X.c
    let Y : Ω → ℝ := fun ω => X.X t ω - X.X s ω - ((t - s) : ℝ) * X.c
    Integrable (Ms * Y) P ∧
      (P[Ms * Y | 𝓕.rightCont s] =ᵐ[P] (fun _ => (0 : ℝ))) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let Ms : Ω → ℝ := fun ω => X.X s ω - (s : ℝ) * X.c
  let Y : Ω → ℝ := fun ω => X.X t ω - X.X s ω - ((t - s) : ℝ) * X.c
  have hτ0events : ∀ u : ℝ≥0,
      MeasurableSet[𝓕.rightCont u] {ω : Ω | (fun _ : Ω => (0 : ℝ≥0)) ω ≤ u} := by
    intro u
    simp
  have hτ0stop : IsStoppingTime 𝓕.rightCont
      (fun ω => ((fun _ : Ω => (0 : ℝ≥0)) ω : WithTop ℝ≥0)) :=
    isStoppingTime_withTop_of_le_events (fun _ : Ω => (0 : ℝ≥0)) hτ0events
  have hτ0bound : ∀ ω : Ω, (fun _ : Ω => (0 : ℝ≥0)) ω ≤ 0 :=
    fun _ => le_rfl
  have hMsMem : MemLp Ms 2 P := by
    have hm :=
      avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
        X hν (fun _ : Ω => (0 : ℝ≥0)) hτ0stop 0 hτ0bound s
    simpa [Ms, X.X_zero] using hm
  have hτsevents : ∀ u : ℝ≥0,
      MeasurableSet[𝓕.rightCont u] {ω : Ω | (fun _ : Ω => s) ω ≤ u} := by
    intro u
    by_cases hsu : s ≤ u <;> simp [hsu]
  have hτsstop : IsStoppingTime 𝓕.rightCont
      (fun ω => ((fun _ : Ω => s) ω : WithTop ℝ≥0)) :=
    isStoppingTime_withTop_of_le_events (fun _ : Ω => s) hτsevents
  have hτsbound : ∀ ω : Ω, (fun _ : Ω => s) ω ≤ s :=
    fun _ => le_rfl
  have hYMem : MemLp Y 2 P := by
    have hm :=
      avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
        X hν (fun _ : Ω => s) hτsstop s hτsbound (t - s)
    simpa only [Y, add_tsub_cancel_of_le hst, NNReal.coe_sub hst] using hm
  have hProdI : Integrable (Ms * Y) P := hMsMem.integrable_mul hYMem
  have hMsStrong : StronglyMeasurable[𝓕.rightCont s] Ms :=
    (((X.adapted s).mono (𝓕.le_rightCont s) le_rfl).sub_const
      ((s : ℝ) * X.c)).stronglyMeasurable
  have hYpair :=
    avram_wave6_03_original_rightCont_gaussian_deterministic_increment_condExp_zero
      X hν s t hst
  have hYI : Integrable Y P := hYpair.1
  have hYCE : P[Y | 𝓕.rightCont s] =ᵐ[P] (fun _ => (0 : ℝ)) :=
    hYpair.2
  have hPull : P[Ms * Y | 𝓕.rightCont s] =ᵐ[P]
      Ms * P[Y | 𝓕.rightCont s] :=
    condExp_mul_of_stronglyMeasurable_left hMsStrong hProdI hYI
  change Integrable (Ms * Y) P ∧
    (P[Ms * Y | 𝓕.rightCont s] =ᵐ[P] (fun _ => (0 : ℝ)))
  refine ⟨hProdI, ?_⟩
  filter_upwards [hPull, hYCE] with ω hp hz
  calc
    (P[Ms * Y | 𝓕.rightCont s]) ω =
        (Ms * P[Y | 𝓕.rightCont s]) ω := hp
    _ = Ms ω * (P[Y | 𝓕.rightCont s]) ω := rfl
    _ = 0 := by rw [hz]; ring
