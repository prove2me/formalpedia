-- Prove2me | solution 1 for DivideChooseBayes.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:09:01.229308+00:00
-- url     : https://prove2.me/submissions/c60db493-846f-4342-8a2c-e8bcd5540b04

import Mathlib
import Definitions.Def_DivideChooseBayes_chooserUtility
import Definitions.Def_DivideChooseBayes_IsOptimalDivision

open MeasureTheory ProbabilityTheory

open DivideChooseBayes in
theorem solution {ι : Type*} [Fintype ι] (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ]
    (gD : ι → ℝ) :
    (∀ q : ι → ℝ, IsDivision q → ∀ gC : ι → ℝ, 1 / 2 * ∑ i, gC i ≤ chooserUtility gD q gC) ∧
      ∀ q : ι → ℝ, IsOptimalDivision μ gD q → 1 / 2 * ∑ i, gD i ≤ interimUtility μ gD q := by
  have hsum : ∀ x q : ι → ℝ, pileOneValue x q + pileTwoValue x q = ∑ i, x i := by
    intro x q
    unfold pileOneValue pileTwoValue
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  refine ⟨?_, ?_⟩
  · intro q _ gC
    have hs := hsum gC q
    unfold chooserUtility
    by_cases h : ChoosesPileOne gD q gC
    · simp only [h, ↓reduceIte]
      rcases h with h | ⟨h, _⟩ <;> linarith
    · simp only [h, ↓reduceIte]
      unfold ChoosesPileOne at h
      push_neg at h
      linarith [h.1]
  · intro q hq
    have h0 : IsDivision (0 : ι → ℝ) := fun i => ⟨by norm_num, by norm_num⟩
    refine le_trans ?_ (hq.2 0 h0)
    have hconst : ∀ gC, dividerUtility gD 0 gC = 1 / 2 * ∑ i, gD i := by
      intro gC
      unfold dividerUtility
      by_cases h : ChoosesPileOne gD 0 gC
      · simp only [h, ↓reduceIte]
        simp only [pileTwoValue, pOfQ, Pi.zero_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      · simp only [h, ↓reduceIte]
        simp only [pileOneValue, pOfQ, Pi.zero_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring)
    unfold interimUtility
    simp_rw [hconst]
    rw [integral_const]
    simp
