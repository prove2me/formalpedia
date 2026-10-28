-- Prove2me | solution 1 for AvramDividend.Classical.ae_injective_active_arrivals_of_product_restricted_pair_laws
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:19:43.835141+00:00
-- url     : https://prove2.me/submissions/b04ff034-0424-4f6c-aa81-7a2034928ac2

import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.IdentDistrib
import Theorems.Thm_AvramDividend_Classical_ae_injective_on_active_indices_of_pairwise_ae
import Theorems.Thm_AvramDividend_Classical_ae_distinct_of_joint_product_atomless

open AvramDividend.Classical MeasureTheory
open scoped ENNReal

theorem solution
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    (P : Measure Ω) (active : ι → Ω → Prop) (τ : ι → Ω → ℝ)
    (hactive : ∀ i, MeasurableSet {ω : Ω | active i ω})
    (hmeas : ∀ i j, Measurable (fun ω : Ω => (τ i ω, τ j ω)))
    (μ ν : ι → ι → Measure ℝ)
    (hSFinite : ∀ i j, SFinite (ν i j))
    (hNull : ∀ i j, NullSingletonClass (ν i j))
    (hjoint : ∀ i j : ι, i ≠ j →
      (P.restrict {ω : Ω | active i ω ∧ active j ω}).map
        (fun ω => (τ i ω, τ j ω)) = (μ i j).prod (ν i j)) :
    ∀ᵐ ω ∂P, ∀ i j : ι,
      active i ω → active j ω → τ i ω = τ j ω → i = j := by
  refine ae_injective_on_active_indices_of_pairwise_ae P active τ (fun i j hij => ?_)
  haveI := hSFinite i j
  haveI := hNull i j
  have h := ae_distinct_of_joint_product_atomless (P.restrict {ω : Ω | active i ω ∧ active j ω})
    (τ i) (τ j) (hmeas i j) (μ i j) (ν i j) (hjoint i j hij)
  rw [ae_restrict_iff' (show MeasurableSet {ω : Ω | active i ω ∧ active j ω} from (hactive i).inter (hactive j))] at h
  filter_upwards [h] with ω hω hi hj
  exact hω ⟨hi, hj⟩
