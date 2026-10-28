-- Prove2me | solution 1 for AvramDividend.Classical.ae_injective_on_active_of_pairwise_product_law_atomless
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T07:37:10.50786+00:00
-- url     : https://prove2.me/submissions/0f1ea26b-7e2d-47ec-86ad-8f6d176ffcea

import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Theorems.Thm_AvramDividend_Classical_ae_injective_of_pairwise_product_law_atomless

open AvramDividend.Classical MeasureTheory
open scoped ENNReal
theorem solution
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (active : ι → Prop) (τ : ι → Ω → ℝ)
    (hτ : ∀ i, Measurable (τ i))
    (hpair : ∀ i j, active i → active j → i ≠ j →
      Measure.map (fun ω => (τ i ω, τ j ω)) P =
        (Measure.map (τ i) P).prod (Measure.map (τ j) P))
    (hatom : ∀ i, active i →
      NullSingletonClass (Measure.map (τ i) P)) :
    ∀ᵐ ω ∂P, Set.InjOn (fun i : ι => τ i ω) {i | active i} := by
  have h := ae_injective_of_pairwise_product_law_atomless P (ι := {i // active i})
    (fun i => τ i.1) (fun i => hτ i.1)
    (fun i j hij => hpair i.1 j.1 i.2 j.2 (fun h => hij (Subtype.ext h))) (fun j => hatom j.1 j.2)
  filter_upwards [h] with ω hω
  intro i hi j hj hij
  exact congrArg Subtype.val (hω (a₁ := ⟨i, hi⟩) (a₂ := ⟨j, hj⟩) hij)
