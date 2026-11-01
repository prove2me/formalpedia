-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_iid_mark_fixed_sum_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T15:08:17.220981+00:00
-- url     : https://prove2.me/submissions/e29d4c4c-8ba5-4710-ac98-36d077f4cc74

import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_iid_mark_finite_sum_mean_variance

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped ENNReal NNReal Nat

/-- The raw squared iid mark-block moment, including all off-diagonal mean
terms, is derived from independence and the variance theorem. -/
theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (Y : ℕ → Ω → E) (hYm : ∀ i, Measurable (Y i))
    (hYL : ∀ i, HasLaw (Y i) ν P) (hYi : iIndepFun Y P)
    (f : E → ℝ) (hf : Measurable f) (hfI : Integrable f ν)
    (hf2 : MemLp f 2 ν) (j : ℕ) :
    (∫ ω, (∑ i ∈ Finset.range j, f (Y i ω)) ^ 2 ∂P) =
      (j : ℝ) * (∫ z, f z ^ 2 ∂ν) +
        (j : ℝ) * ((j : ℝ) - 1) * (∫ z, f z ∂ν) ^ 2 := by
  have hXi (i : ℕ) : MemLp (fun ω => f (Y i ω)) 2 P := by
    simpa [Function.comp_def] using
      hf2.comp_measurePreserving ((hYL i).measurePreserving (hYm i))
  have hLp :
      MemLp (fun ω => ∑ i ∈ Finset.range j, f (Y i ω)) 2 P :=
    memLp_finset_sum (Finset.range j) (fun i hi => hXi i)
  have hFixed :=
    avram_wave4_p1_iid_mark_finite_sum_mean_variance
      P ν Y hYm hYL hYi f hf hfI hf2 (Finset.range j)
  have hCard : (Finset.range j).card = j := Finset.card_range j
  have hMean :
      (∫ ω, ∑ i ∈ Finset.range j, f (Y i ω) ∂P) =
        (j : ℝ) * ∫ z, f z ∂ν := by
    simpa only [hCard] using hFixed.1
  have hVar :
      variance (fun ω => ∑ i ∈ Finset.range j, f (Y i ω)) P =
        (j : ℝ) * variance f ν := by
    simpa only [hCard] using hFixed.2
  calc
    (∫ ω, (∑ i ∈ Finset.range j, f (Y i ω)) ^ 2 ∂P) =
        variance (fun ω => ∑ i ∈ Finset.range j, f (Y i ω)) P +
          (∫ ω, ∑ i ∈ Finset.range j, f (Y i ω) ∂P) ^ 2 := by
          rw [variance_eq_sub hLp]
          simp only [Pi.pow_apply]
          ring
    _ = (j : ℝ) * variance f ν +
          ((j : ℝ) * ∫ z, f z ∂ν) ^ 2 := by rw [hVar, hMean]
    _ = (j : ℝ) *
          ((∫ z, f z ^ 2 ∂ν) - (∫ z, f z ∂ν) ^ 2) +
          ((j : ℝ) * ∫ z, f z ∂ν) ^ 2 := by
          rw [variance_eq_sub hf2]
          simp only [Pi.pow_apply]
    _ = (j : ℝ) * (∫ z, f z ^ 2 ∂ν) +
          (j : ℝ) * ((j : ℝ) - 1) * (∫ z, f z ∂ν) ^ 2 := by ring
