-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.infinitePi_sum_merge
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:04:56.443083+00:00
-- url     : https://prove2.me/submissions/8fbbe771-d944-4ec4-8ae6-74533587515e

import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

/-- Independent products over two countable index blocks merge to the independent sum-indexed product. -/
theorem solution {ι κ α : Type*} [Countable ι] [Countable κ]
    [MeasurableSpace α] (μ : ι → Measure α) (ν : κ → Measure α)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ j, IsProbabilityMeasure (ν j)] :
    ((Measure.infinitePi μ).prod (Measure.infinitePi ν)).map
      (fun p : (ι → α) × (κ → α) => Sum.elim p.1 p.2) =
        Measure.infinitePi (Sum.elim μ ν) := by
  classical
  letI (x : ι ⊕ κ) : IsProbabilityMeasure (Sum.elim μ ν x) := by cases x <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> infer_instance
  let merge : ((ι → α) × (κ → α)) → (ι ⊕ κ → α) := fun p => Sum.elim p.1 p.2
  have hm : Measurable merge := by
    apply measurable_pi_lambda
    intro x
    cases x with
    | inl i => exact (measurable_pi_apply i).comp measurable_fst
    | inr j => exact (measurable_pi_apply j).comp measurable_snd
  change ((Measure.infinitePi μ).prod (Measure.infinitePi ν)).map merge = _
  apply Measure.eq_infinitePi
  intro S T hT
  have hmeas : MeasurableSet ((S : Set (ι ⊕ κ)).pi T) :=
    MeasurableSet.pi S.countable_toSet (fun i hi => hT i)
  rw [Measure.map_apply hm hmeas]
  have hpre : merge ⁻¹' ((S : Set (ι ⊕ κ)).pi T) =
      ((S.toLeft : Set ι).pi (fun i => T (.inl i))) ×ˢ
        ((S.toRight : Set κ).pi (fun j => T (.inr j))) := by
    ext ⟨x,y⟩
    simp [merge, Set.mem_pi, Finset.mem_toLeft, Finset.mem_toRight, Sum.forall]
  rw [hpre, Measure.prod_prod]
  rw [Measure.infinitePi_pi μ (fun i hi => hT (.inl i)),
      Measure.infinitePi_pi ν (fun j hj => hT (.inr j))]
  rw [← Finset.toLeft_disjSum_toRight (u := S), Finset.prod_disjSum]
  simp
