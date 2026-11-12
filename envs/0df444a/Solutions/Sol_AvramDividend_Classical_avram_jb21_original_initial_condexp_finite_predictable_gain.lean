-- Prove2me | solution 1 for AvramDividend.Classical.avram_jb21_original_initial_condexp_finite_predictable_gain
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T20:16:16.615627+00:00
-- url     : https://prove2.me/submissions/8c333572-feae-49b8-8be3-9b3d97ef7d59

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Theorems.Thm_AvramDividend_Classical_avram_gb66_filtered_predictable_multiplier_condExp_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
noncomputable section

/-- Finite predictable martingale-difference gains remain centred at initial information. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ι : Type*}
    (S : Finset ι)
    (𝓢0 : MeasurableSpace Ω) (𝓢 : ι → MeasurableSpace Ω)
    (h01 : ∀ i ∈ S, 𝓢0 ≤ 𝓢 i)
    (hS : ∀ i ∈ S, 𝓢 i ≤ mΩ)
    (H Q : ι → Ω → ℝ)
    (hH : ∀ i ∈ S, StronglyMeasurable[𝓢 i] (H i))
    (hQ : ∀ i ∈ S, Integrable (Q i) P)
    (hHQ : ∀ i ∈ S,
      Integrable (fun ω => H i ω * Q i ω) P)
    (hQzero : ∀ i ∈ S,
      P[Q i | 𝓢 i] =ᵐ[P] (fun _ => (0 : ℝ))) :
    Integrable (fun ω => ∑ i ∈ S, H i ω * Q i ω) P ∧
    P[(fun ω => ∑ i ∈ S, H i ω * Q i ω) | 𝓢0]
      =ᵐ[P] (fun _ => (0 : ℝ)) := by
  classical
  have hEach (i : ι) (hi : i ∈ S) :
      P[(fun ω => H i ω * Q i ω) | 𝓢0]
        =ᵐ[P] (fun _ => (0 : ℝ)) := by
    have hc :=
      avram_gb66_filtered_predictable_multiplier_condExp_zero
        (mΩ := mΩ) (P := P) (𝓢 i) (H i) (Q i) (hH i hi)
        (hHQ i hi) (hQ i hi) (hQzero i hi)
    have ht :
        P[P[(fun ω => H i ω * Q i ω) | 𝓢 i] | 𝓢0]
          =ᵐ[P] P[(fun ω => H i ω * Q i ω) | 𝓢0] :=
      condExp_condExp_of_le (h01 i hi) (hS i hi)
    have hz :
        P[P[(fun ω => H i ω * Q i ω) | 𝓢 i] | 𝓢0]
          =ᵐ[P] P[(fun _ => (0 : ℝ)) | 𝓢0] :=
      condExp_congr_ae hc
    exact ht.symm.trans (hz.trans (by simp))
  have hs :=
    condExp_finset_sum hHQ 𝓢0
  have hFun :
      (∑ i ∈ S, fun ω => H i ω * Q i ω) =
        (fun ω => ∑ i ∈ S, H i ω * Q i ω) := by
    funext ω
    simp only [Finset.sum_apply]
  rw [hFun] at hs
  have hall : ∀ᵐ ω ∂P, ∀ i ∈ S,
      P[(fun ω => H i ω * Q i ω) | 𝓢0] ω = 0 :=
    (Filter.eventually_all_finset S).2 (fun i hi => hEach i hi)
  refine ⟨integrable_finset_sum S hHQ, ?_⟩
  filter_upwards [hs, hall] with ω hsω hω
  calc
    P[(fun ω => ∑ i ∈ S, H i ω * Q i ω) | 𝓢0] ω =
        ∑ i ∈ S, P[(fun ω => H i ω * Q i ω) | 𝓢0] ω := by simpa only [Finset.sum_apply] using hsω
    _ = 0 := Finset.sum_eq_zero (fun i hi => hω i hi)
