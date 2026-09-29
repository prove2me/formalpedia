-- Prove2me | solution 1 for BanditAlgorithm.bandit_ucb_index_count_bound
-- status  : ACCEPTED   (prove)
-- author  : @MKPynnic
-- created : 2026-07-19T05:20:03.778517+00:00
-- url     : https://prove2.me/submissions/2660c14a-ee12-4834-a78c-efb538431c02

import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Theorems.Thm_BanditAlgorithm_bandit_ucb_index_exponential_sum_bound

open MeasureTheory ProbabilityTheory Real

private lemma event_nullMeasurable
    {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X : ℕ → Ω → ℝ}
    (h_subG : ∀ i, HasSubgaussianMGF (X i) 1 P)
    (t : ℕ) (ε a : ℝ) :
    NullMeasurableSet {ω |
      ε ≤ (∑ s ∈ Finset.range t, X s ω) / t + Real.sqrt (2 * a / t)} P := by
  apply nullMeasurableSet_le aemeasurable_const
  have hXm (i : ℕ) : AEMeasurable (X i) P := (h_subG i).aemeasurable
  fun_prop

private lemma indicator_integrable
    {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {X : ℕ → Ω → ℝ}
    (h_subG : ∀ i, HasSubgaussianMGF (X i) 1 P)
    (t : ℕ) (ε a : ℝ) :
    Integrable (fun ω ↦ if ε ≤ (∑ s ∈ Finset.range t, X s ω) / t +
      Real.sqrt (2 * a / t) then (1 : ℝ) else 0) P := by
  have hm := event_nullMeasurable h_subG t ε a
  refine ((integrable_const (μ := P) (c := (1 : ℝ))).indicator₀ hm).congr ?_
  filter_upwards with ω
  simp [Set.indicator_apply]

private lemma event_rewrite_sum
    {Ω : Type} {X : ℕ → Ω → ℝ}
    (t : ℕ) (ht : 1 ≤ t) (ε a : ℝ) :
    {ω | ε ≤ (∑ s ∈ Finset.range t, X s ω) / t + Real.sqrt (2 * a / t)} =
      {ω | (t : ℝ) * (ε - Real.sqrt (2 * a / t)) ≤
        ∑ s ∈ Finset.range t, X s ω} := by
  ext ω
  simp only [Set.mem_setOf_eq]
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  constructor <;> intro h
  · have h' : ε - Real.sqrt (2 * a / t) ≤
        (∑ s ∈ Finset.range t, X s ω) / t := by linarith
    have := (le_div_iff₀ ht0).mp h'
    nlinarith
  · have h' : (ε - Real.sqrt (2 * a / t)) * (t : ℝ) ≤
        ∑ s ∈ Finset.range t, X s ω := by nlinarith
    have := (le_div_iff₀ ht0).mpr h'
    linarith

theorem solution
    {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ}
    (h_indep : iIndepFun X P)
    (h_subG : ∀ i, HasSubgaussianMGF (X i) 1 P)
    {n : ℕ} {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a) :
    ∫ ω, (∑ t ∈ Finset.Icc 1 n,
        if ε ≤ (∑ s ∈ Finset.range t, X s ω) / t + Real.sqrt (2 * a / t)
          then (1 : ℝ) else 0) ∂P ≤
      1 + 2 / ε ^ 2 * (a + Real.sqrt (Real.pi * a) + 1) := by
  rw [integral_finset_sum]
  · calc
      (∑ t ∈ Finset.Icc 1 n, ∫ ω,
          (if ε ≤ (∑ s ∈ Finset.range t, X s ω) / t + Real.sqrt (2 * a / t)
            then (1 : ℝ) else 0) ∂P) =
          ∑ t ∈ Finset.Icc 1 n, P.real {ω |
            ε ≤ (∑ s ∈ Finset.range t, X s ω) / t + Real.sqrt (2 * a / t)} := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [show (fun ω ↦ if ε ≤ (∑ s ∈ Finset.range t, X s ω) / t +
            Real.sqrt (2 * a / t) then (1 : ℝ) else 0) =
            Set.indicator {ω | ε ≤ (∑ s ∈ Finset.range t, X s ω) / t +
              Real.sqrt (2 * a / t)} (fun _ ↦ (1 : ℝ)) by
              funext ω
              simp only [Set.indicator, Set.mem_setOf_eq]]
        rw [integral_indicator₀ (event_nullMeasurable h_subG t ε a)]
        simpa using setIntegral_const (μ := P) (s := {ω |
          ε ≤ (∑ s ∈ Finset.range t, X s ω) / t + Real.sqrt (2 * a / t)}) (1 : ℝ)
      _ ≤ ∑ t ∈ Finset.Icc 1 n,
          if 2 * a / ε ^ 2 < (t : ℝ) then
            Real.exp (-((t : ℝ) * (ε - Real.sqrt (2 * a / t))) ^ 2 /
              ((2 : ℝ) * (t : ℝ) * (1 : ℝ)))
          else 1 := by
        apply Finset.sum_le_sum
        intro t ht
        split_ifs with hlarge
        · have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
          have ht0 : (0 : ℝ) < t := by exact_mod_cast ht1
          have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
          have hmul : 2 * a < (t : ℝ) * ε ^ 2 := by
            have := (div_lt_iff₀ hε2).mp hlarge
            nlinarith
          have hratio : 2 * a / (t : ℝ) < ε ^ 2 :=
            (div_lt_iff₀ ht0).mpr (by nlinarith)
          have hsqrt : Real.sqrt (2 * a / (t : ℝ)) ≤ ε :=
            Real.sqrt_le_iff.mpr ⟨hε.le, hratio.le⟩
          rw [event_rewrite_sum t ht1 ε a]
          simpa using HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun
            (n := t) (c := 1) h_indep (fun i hi ↦ h_subG i)
              (mul_nonneg ht0.le (sub_nonneg.mpr hsqrt))
        · exact measureReal_le_one
      _ ≤ 1 + 2 / ε ^ 2 * (a + Real.sqrt (Real.pi * a) + 1) :=
        BanditAlgorithm.bandit_ucb_index_exponential_sum_bound hε ha
  · intro t ht
    exact indicator_integrable h_subG t ε a
