-- Prove2me | solution 1 for AvramDividend.Classical.ae_injective_of_pairwise_product_law_atomless
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T07:23:45.887081+00:00
-- url     : https://prove2.me/submissions/cb2a2cd0-6b28-4a29-b859-af9b17b81772

import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Probability.IdentDistrib
import Theorems.Thm_AvramDividend_Classical_prod_ae_distinct_of_atomless_second
import Theorems.Thm_AvramDividend_Classical_ae_injective_of_pairwise_ae_distinct

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped ENNReal

theorem solution
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (τ : ι → Ω → ℝ)
    (hτ : ∀ i, Measurable (τ i))
    (hpair : ∀ i j : ι, i ≠ j →
      Measure.map (fun ω => (τ i ω, τ j ω)) P =
        (Measure.map (τ i) P).prod (Measure.map (τ j) P))
    (hatom : ∀ j : ι, NullSingletonClass (Measure.map (τ j) P)) :
    ∀ᵐ ω ∂P, Function.Injective (fun i : ι => τ i ω) := by
  apply ae_injective_of_pairwise_ae_distinct P τ
  intro i j hij
  letI : NullSingletonClass (Measure.map (τ j) P) := hatom j
  have hprod := prod_ae_distinct_of_atomless_second
    (Measure.map (τ i) P) (Measure.map (τ j) P)
  rw [← hpair i j hij] at hprod
  have hm : Measurable (fun ω => (τ i ω, τ j ω)) :=
    (hτ i).prodMk (hτ j)
  have hset : MeasurableSet {p : ℝ × ℝ | p.1 ≠ p.2} :=
    (isClosed_eq continuous_fst continuous_snd).measurableSet.compl
  exact (ae_map_iff hm.aemeasurable hset).mp hprod