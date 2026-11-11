-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18g_original_smallband_cutoff_rightcont_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T23:51:56.161903+00:00
-- url     : https://prove2.me/submissions/d02ddd5d-2359-4b9b-911c-52d0c277a488

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ja18j_public_original_compensated_finsum
import Theorems.Thm_AvramDividend_Classical_avram_ja18f_finite_marked_step_sum_right_continuous
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section

/-- Every finite compensated marked cutoff on the original sample space
is a finite right-continuous step sum minus continuous deterministic drift. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∀ (n : ℕ) (ω : Ω),
      (∀ t : ℝ≥0,
        ContinuousWithinAt
          (fun s : ℝ≥0 =>
            avram_p4_h_gaussian_intrinsic_small_band_compensated X n s ω)
          (Ici t) t) ∧
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n 0 ω = 0 := by
  classical
  intro n ω
  let j (u : ℝ≥0) : ℝ :=
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
  let c : ℝ := ∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))), z ∂X.ν
  constructor
  · intro t
    let T : ℝ≥0 := t + 1
    have htT : t < T := by simp [T]
    obtain ⟨F, hF, _⟩ :=
      avram_ja18j_public_original_compensated_finsum
        X n T ω
    have hEq (s : ℝ≥0) (hsT : s ≤ T) :
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n s ω =
          (∑ u ∈ F, if u ≤ s then j u else 0) - (s : ℝ) * c := by
      obtain ⟨Fs, hFs, hIds⟩ :=
        avram_ja18j_public_original_compensated_finsum
          X n s ω
      have hFilt : Fs = F.filter (fun u => u ≤ s) := by
        ext u
        constructor
        · intro hu
          obtain ⟨hu0, hus, huLower, huUpper⟩ := (hFs u).mp hu
          apply Finset.mem_filter.mpr
          exact ⟨(hF u).mpr ⟨hu0, hus.trans hsT, huLower, huUpper⟩, hus⟩
        · intro hu
          obtain ⟨huF, hus⟩ := Finset.mem_filter.mp hu
          obtain ⟨hu0, _, huLower, huUpper⟩ := (hF u).mp huF
          exact (hFs u).mpr ⟨hu0, hus, huLower, huUpper⟩
      rw [hFilt] at hIds
      simpa only [j, c, Finset.sum_filter] using hIds
    have hStep :
        ContinuousWithinAt
          (fun s : ℝ≥0 => ∑ u ∈ F, if u ≤ s then j u else 0)
          (Ici t) t := by
      simpa using
        (avram_ja18f_finite_marked_step_sum_right_continuous
          F (fun u : ℝ≥0 => u) j t)
    have hDrift :
        ContinuousWithinAt (fun s : ℝ≥0 => (s : ℝ) * c) (Ici t) t := by
      fun_prop
    have hLimit := hStep.sub hDrift
    have hEv : ∀ᶠ s : ℝ≥0 in 𝓝[Ici t] t, s ≤ T := by
      filter_upwards [(eventually_lt_nhds htT).filter_mono
        nhdsWithin_le_nhds] with s hs
      exact le_of_lt hs
    have hEventual :
        (fun s : ℝ≥0 =>
            avram_p4_h_gaussian_intrinsic_small_band_compensated X n s ω)
          =ᶠ[𝓝[Ici t] t]
        (fun s : ℝ≥0 => (∑ u ∈ F, if u ≤ s then j u else 0) -
          (s : ℝ) * c) := by
      filter_upwards [hEv] with s hs
      exact hEq s hs
    change Tendsto
      (fun s : ℝ≥0 =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n s ω)
      (𝓝[Ici t] t)
      (𝓝 (avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω))
    rw [hEq t (le_of_lt htT)]
    exact hLimit.tendsto.congr' hEventual.symm
  · obtain ⟨F, hF, hId⟩ :=
      avram_ja18j_public_original_compensated_finsum
        X n 0 ω
    have hEmpty : F = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro u hu
      have hu0 := (hF u).mp hu
      exact (not_lt_of_ge hu0.2.1) hu0.1
    simpa [j, c, hEmpty] using hId
