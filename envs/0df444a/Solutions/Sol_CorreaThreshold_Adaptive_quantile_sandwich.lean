-- Prove2me | solution 1 for CorreaThreshold.Adaptive.quantile_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T20:55:34.605577+00:00
-- url     : https://prove2.me/submissions/69617bf2-37ac-4dd2-a32e-2aab86259555

import Mathlib
import Definitions.Def_CorreaThreshold_Adaptive_Setting

open MeasureTheory ProbabilityTheory CorreaThreshold.Adaptive Filter Topology

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0)
    (q : ℝ) (hq : q ∈ Set.Ioc 0 1) :
    ENNReal.ofReal q ≤ μ (Set.Ici (tauQ μ q)) ∧
      μ (Set.Ioi (tauQ μ q)) ≤ ENNReal.ofReal q ∧
      μ (Set.Ioi (tauQ μ q)) = ENNReal.ofReal (1 - cdf μ (tauQ μ q)) ∧
      (ContinuousAt (cdf μ) (tauQ μ q) →
        μ (Set.Ici (tauQ μ q)) = ENNReal.ofReal q ∧ μ (Set.Ioi (tauQ μ q)) = ENNReal.ofReal q) := by
  obtain ⟨hq0, hq1⟩ := hq
  set F := cdf μ with hF
  set S : Set ℝ := {x : ℝ | 0 ≤ x ∧ 1 - q ≤ F x} with hS
  have htdef : tauQ μ q = sInf S := rfl
  set t := tauQ μ q with ht
  -- S is nonempty and bounded below
  have hne : S.Nonempty := by
    have hlim := tendsto_cdf_atTop μ
    have hev : ∀ᶠ x in atTop, 1 - q < F x := hlim.eventually (lt_mem_nhds (by linarith))
    obtain ⟨x, hx⟩ := (hev.and (eventually_ge_atTop 0)).exists
    exact ⟨x, hx.2, hx.1.le⟩
  have hbdd : BddBelow S := ⟨0, fun x hx => hx.1⟩
  have ht0 : 0 ≤ t := by rw [htdef]; exact le_csInf hne (fun x hx => hx.1)
  -- (A) `1 - q ≤ F t`
  have hA : 1 - q ≤ F t := by
    have hrc : ContinuousWithinAt F (Set.Ici t) t := F.right_continuous t
    have hT : Tendsto F (𝓝[>] t) (𝓝 (F t)) :=
      hrc.tendsto.mono_left (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
    apply ge_of_tendsto hT
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx' : sInf S < x := by rw [← htdef]; exact hx
    obtain ⟨s, hs, hsx⟩ := exists_lt_of_csInf_lt hne hx'
    exact le_trans hs.2 (monotone_cdf μ hsx.le)
  -- (B) `leftLim F t ≤ 1 - q`
  have hB : Function.leftLim F t ≤ 1 - q := by
    rcases eq_or_lt_of_le ht0 with h | h
    · have hI := F.measure_Iio (tendsto_cdf_atBot μ) t
      rw [measure_cdf, ← h, hμ, sub_zero, eq_comm, ENNReal.ofReal_eq_zero] at hI
      rw [← h]
      linarith
    · have hT := (monotone_cdf μ).tendsto_leftLim t
      apply le_of_tendsto hT
      filter_upwards [Ioo_mem_nhdsLT h] with x hx
      have hx' : x < sInf S := by rw [← htdef]; exact hx.2
      have hnot := notMem_of_lt_csInf hx' hbdd
      simp only [hS, Set.mem_setOf_eq, not_and, not_le] at hnot
      exact (hnot hx.1.le).le
  have hIci : μ (Set.Ici t) = ENNReal.ofReal (1 - Function.leftLim F t) := by
    have := F.measure_Ici (tendsto_cdf_atTop μ) t
    rwa [measure_cdf] at this
  have hIoi : μ (Set.Ioi t) = ENNReal.ofReal (1 - F t) := by
    have := F.measure_Ioi (tendsto_cdf_atTop μ) t
    rwa [measure_cdf] at this
  refine ⟨?_, ?_, hIoi, ?_⟩
  · rw [hIci]; exact ENNReal.ofReal_le_ofReal (by linarith)
  · rw [hIoi]; exact ENNReal.ofReal_le_ofReal (by linarith)
  · intro hc
    have hL : Function.leftLim F t = F t :=
      leftLim_eq_of_tendsto (hc.tendsto.mono_left nhdsWithin_le_nhds)
    refine ⟨?_, ?_⟩
    · rw [hIci]; congr 1; linarith
    · rw [hIoi]; congr 1; linarith
