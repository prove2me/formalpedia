-- Prove2me | solution 1 for FeinbergPOMDP.WStar.theorem_5_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T18:04:24.308633+00:00
-- url     : https://prove2.me/submissions/63fdd6c1-37a1-4e77-b9a3-4965ce967360

import Mathlib
import Definitions.Def_FeinbergPOMDP_WStar_Model

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter FeinbergPOMDP.WStar

/-- The one-sided estimate (5.18)–(5.20) of the paper: `μ{hₙ - h ≥ ε} → 0`. -/
lemma fpw55_plus {S : Type*} [MeasurableSpace S]
    (h : S → ℝ) (hs : ℕ → S → ℝ) (hh : Measurable h) (hhs : ∀ n, Measurable (hs n))
    (M : ℝ) (hM0 : 0 < M) (hMh : ∀ s, |h s| ≤ M) (hMhs : ∀ n s, |hs n s| ≤ M)
    (μ : ProbabilityMeasure S) (μs : ℕ → ProbabilityMeasure S) (hμ : TendstoTV μs μ)
    (h517 : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n → ∀ B : Set S, MeasurableSet B →
      |∫ s in B, hs n s ∂(μs n : Measure S) - ∫ s in B, h s ∂(μ : Measure S)| ≤ ε)
    (ε : ℝ) (hε : 0 < ε) (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n, N ≤ n → (μ : Measure S).real {s | ε ≤ hs n s - h s} ≤ η := by
  have hint : ∀ (m : Measure S) [IsProbabilityMeasure m] (g : S → ℝ), Measurable g →
      (∀ t, |g t| ≤ M) → Integrable g m := fun m _ g hg hg1 =>
    Integrable.of_bound hg.aestronglyMeasurable M
      (Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact hg1 t)
  obtain ⟨N1, hN1⟩ := h517 (η * ε / 4) (by positivity)
  obtain ⟨N2, hN2⟩ := hμ (η * ε / (4 * M)) (by positivity)
  obtain ⟨N3, hN3⟩ := hμ (η / 2) (by positivity)
  refine ⟨max N1 (max N2 N3), fun n hn => ?_⟩
  have hn1 : N1 ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : N2 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn3 : N3 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  set B := {s | ε ≤ hs n s - h s} with hB
  have hBm : MeasurableSet B := measurableSet_le measurable_const ((hhs n).sub hh)
  set ν : Measure S := (μs n : Measure S) with hν
  -- (5.18): ε ν(B) ≤ ∫_B hₙ dν - ∫_B h dν
  have h1 : ε * ν.real B ≤ ∫ s in B, hs n s ∂ν - ∫ s in B, h s ∂ν := by
    rw [← integral_sub (hint ν _ (hhs n) (hMhs n)).integrableOn (hint ν _ hh hMh).integrableOn]
    have := setIntegral_mono_on (μ := ν) (s := B) (f := fun _ => ε)
      (g := fun s => hs n s - h s) (integrableOn_const (by simp))
      ((hint ν _ (hhs n) (hMhs n)).sub (hint ν _ hh hMh)).integrableOn hBm (fun s hs => hs)
    rw [setIntegral_const, smul_eq_mul, mul_comm] at this
    exact this
  -- (5.17)
  have h2 : ∫ s in B, hs n s ∂ν - ∫ s in B, h s ∂(μ : Measure S) ≤ η * ε / 4 :=
    le_trans (le_abs_self _) (hN1 n hn1 B hBm)
  -- (5.19), first part, through the test function `1_B h / M`
  have h3 : ∫ s in B, h s ∂(μ : Measure S) - ∫ s in B, h s ∂ν ≤ η * ε / 4 := by
    have := hN2 n hn2 (B.indicator fun s => h s / M) ((hh.div_const M).indicator hBm)
      (fun s => by
        by_cases hsB : s ∈ B
        · simp only [Set.indicator_of_mem hsB, abs_div, abs_of_pos hM0]
          exact (div_le_one hM0).2 (hMh s)
        · simp [Set.indicator_of_notMem hsB])
    rw [integral_indicator hBm, integral_indicator hBm, integral_div, integral_div,
      ← sub_div, abs_div, abs_of_pos hM0, div_le_iff₀ hM0, abs_sub_comm] at this
    have e : η * ε / (4 * M) * M = η * ε / 4 := by field_simp
    rw [e] at this
    exact le_trans (le_abs_self _) this
  have hνB : ν.real B ≤ η / 2 := by
    have : ε * ν.real B ≤ ε * (η / 2) := by nlinarith
    exact le_of_mul_le_mul_left this hε
  -- (5.19), second part
  have h4 : (μ : Measure S).real B - ν.real B ≤ η / 2 := by
    have := hN3 n hn3 (B.indicator 1) (measurable_one.indicator hBm)
      (fun s => by by_cases hsB : s ∈ B <;> simp [Set.indicator, hsB])
    rw [integral_indicator_one hBm, integral_indicator_one hBm, abs_sub_comm] at this
    exact le_trans (le_abs_self _) this
  linarith

theorem solution {S : Type*}
    [TopologicalSpace S] [TopologicalSpace.MetrizableSpace S] [MeasurableSpace S] [BorelSpace S]
    (h : S → ℝ) (hs : ℕ → S → ℝ) (hh : Measurable h) (hhs : ∀ n, Measurable (hs n))
    (hbd : ∃ M : ℝ, (∀ s, |h s| ≤ M) ∧ ∀ n s, |hs n s| ≤ M)
    (μ : ProbabilityMeasure S) (μs : ℕ → ProbabilityMeasure S) (hμ : TendstoTV μs μ)
    (h517 : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n → ∀ B : Set S, MeasurableSet B →
      |∫ s in B, hs n s ∂(μs n : Measure S) - ∫ s in B, h s ∂(μ : Measure S)| ≤ ε) :
    TendstoInMeasure (μ : Measure S) hs atTop h ∧
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ᵐ s ∂(μ : Measure S), Tendsto (fun k => hs (φ k) s) atTop (𝓝 (h s)) := by
  obtain ⟨M0, hMh0, hMhs0⟩ := hbd
  set M := |M0| + 1 with hM
  have hM0 : 0 < M := by positivity
  have hMh : ∀ s, |h s| ≤ M := fun s => by linarith [hMh0 s, le_abs_self M0]
  have hMhs : ∀ n s, |hs n s| ≤ M := fun n s => by linarith [hMhs0 n s, le_abs_self M0]
  have hMh' : ∀ s, |(-h) s| ≤ M := fun s => by simpa using hMh s
  have hMhs' : ∀ n s, |(fun n => -hs n) n s| ≤ M := fun n s => by simpa using hMhs n s
  have h517' : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n → ∀ B : Set S, MeasurableSet B →
      |∫ s in B, (fun n => -hs n) n s ∂(μs n : Measure S) - ∫ s in B, (-h) s ∂(μ : Measure S)|
        ≤ ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := h517 ε hε
    refine ⟨N, fun n hn B hB => ?_⟩
    have := hN n hn B hB
    simp only [Pi.neg_apply, integral_neg]
    rw [← abs_neg]; convert this using 2; ring
  have hTIM : TendstoInMeasure (μ : Measure S) hs atTop h := by
    rw [tendstoInMeasure_iff_measureReal_dist]
    intro ε hε
    rw [Metric.tendsto_atTop]
    intro η hη
    obtain ⟨N1, hN1⟩ := fpw55_plus h hs hh hhs M hM0 hMh hMhs μ μs hμ h517 ε hε (η / 3)
      (by positivity)
    obtain ⟨N2, hN2⟩ := fpw55_plus (-h) (fun n => -hs n) hh.neg (fun n => (hhs n).neg) M hM0
      hMh' hMhs' μ μs hμ h517' ε hε (η / 3) (by positivity)
    refine ⟨max N1 N2, fun n hn => ?_⟩
    have hsub : {x | ε ≤ dist (hs n x) (h x)} ⊆
        {s | ε ≤ hs n s - h s} ∪ {s | ε ≤ (fun n => -hs n) n s - (-h) s} := by
      intro x hx
      simp only [Set.mem_setOf_eq, Real.dist_eq] at hx
      simp only [Set.mem_union, Set.mem_setOf_eq, Pi.neg_apply]
      rcases le_total 0 (hs n x - h x) with h0 | h0
      · rw [abs_of_nonneg h0] at hx; left; exact hx
      · rw [abs_of_nonpos h0] at hx; right; linarith
    have hle := (measureReal_mono (μ := (μ : Measure S)) hsub (measure_ne_top _ _)).trans
      (measureReal_union_le _ _)
    have a1 := hN1 n (le_trans (le_max_left _ _) hn)
    have a2 := hN2 n (le_trans (le_max_right _ _) hn)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
    linarith
  exact ⟨hTIM, hTIM.exists_seq_tendsto_ae⟩
