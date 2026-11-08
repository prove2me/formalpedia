-- Prove2me | solution 1 for DivideChooseBayes.eq_10
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:16:22.4892+00:00
-- url     : https://prove2.me/submissions/79acaff7-9d49-4c5a-9d87-444a89d2c299

import Mathlib
import Definitions.Def_DivideChooseBayes_IsDivision
import Definitions.Def_DivideChooseBayes_interimUtility
import Definitions.Def_DivideChooseBayes_pileOneProb

open MeasureTheory ProbabilityTheory

open DivideChooseBayes in
theorem solution {ι : Type*} [Fintype ι] (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ]
    (gD q : ι → ℝ) (hq : IsDivision q) :
    interimUtility μ gD q = ∑ i, gD i / 2 + (1 / 2 - pileOneProb μ gD q) * ∑ i, q i * gD i := by
  set S : Set (ι → ℝ) := {gC | ChoosesPileOne gD q gC} with hSdef
  have h1 : Measurable (fun gC : ι → ℝ => pileOneValue gC q) := by
    unfold pileOneValue
    exact (by fun_prop : Continuous fun gC : ι → ℝ => ∑ i, pOfQ q i * gC i).measurable
  have h2 : Measurable (fun gC : ι → ℝ => pileTwoValue gC q) := by
    unfold pileTwoValue
    exact (by fun_prop : Continuous fun gC : ι → ℝ => ∑ i, (1 - pOfQ q i) * gC i).measurable
  have hS : MeasurableSet S := by
    have e : S = {gC | pileTwoValue gC q < pileOneValue gC q} ∪
        ({gC | pileOneValue gC q = pileTwoValue gC q} ∩
          {_gC | pileOneValue gD q < pileTwoValue gD q}) := by
      ext gC
      simp only [hSdef, Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff, ChoosesPileOne]
    rw [e]
    exact (measurableSet_lt h2 h1).union ((measurableSet_eq_fun h1 h2).inter (MeasurableSet.const _))
  have hpt : ∀ gC, dividerUtility gD q gC =
      (∑ i, gD i / 2 + 1 / 2 * ∑ i, q i * gD i) - S.indicator (fun _ => ∑ i, q i * gD i) gC := by
    intro gC
    unfold dividerUtility
    by_cases h : ChoosesPileOne gD q gC
    · simp only [h, ite_true]
      rw [Set.indicator_of_mem (show gC ∈ S from h)]
      unfold pileTwoValue pOfQ
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    · simp only [h, ite_false]
      rw [Set.indicator_of_notMem (show gC ∉ S from h), sub_zero]
      unfold pileOneValue pOfQ
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
  unfold interimUtility pileOneProb
  simp_rw [hpt]
  rw [integral_sub (integrable_const _) ((integrable_const _).indicator hS), integral_const,
    integral_indicator hS, setIntegral_const, probReal_univ, one_smul, smul_eq_mul]
  ring
