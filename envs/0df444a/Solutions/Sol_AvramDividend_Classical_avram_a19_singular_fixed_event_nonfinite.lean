-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_singular_fixed_event_nonfinite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T13:02:14.616813+00:00
-- url     : https://prove2.me/submissions/00f2a487-e62f-4bcb-9347-1f3a2239b9ec

import Mathlib.Probability.Distributions.Geometric
import Theorems.Thm_AvramDividend_Classical_avram_a19_singular_geometric_not_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
noncomputable section

/-- A single positive-probability event controls all geometric source sections. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (A : Set Ω) (hA : P A ≠ 0)
    (p : unitInterval) (hp : p ≠ 0) (hhalf : (p : Real) = 1 / 2)
    (y : Nat → Real)
    (hy : ∀ k, 0 < y k)
    (hsmall : ∀ k, y k ≤ 1 / 16)
    (hpower : ∀ k, y k ≤ 1 / ((2 : Real) ^ k) ^ 2)
    (f : Ω × Nat → Real)
    (hf_meas : AEStronglyMeasurable f (P.prod (geometricMeasure p)))
    (hdom : ∀ ω ∈ A, ∀ k,
      ‖-(3 + y k - 4 * Real.sqrt (y k) - 2 / Real.sqrt (y k))‖ ≤
        ‖f (ω, k)‖) :
    ¬ HasFiniteIntegral f (P.prod (geometricMeasure p)) := by
  intro hfinite
  have hf : Integrable f (P.prod (geometricMeasure p)) :=
    ⟨hf_meas, hfinite⟩
  have hsections : ∀ᵐ ω ∂P,
      Integrable (fun k : Nat => f (ω, k)) (geometricMeasure p) :=
    hf.prod_right_ae
  obtain ⟨ω, hωA, hω_int⟩ :=
    P.exists_mem_of_measure_ne_zero_of_ae hA
      (ae_restrict_of_ae hsections)
  let g : Nat → Real := fun k =>
    -(3 + y k - 4 * Real.sqrt (y k) - 2 / Real.sqrt (y k))
  have hg_meas : AEStronglyMeasurable g (geometricMeasure p) :=
    (measurable_of_countable g).aestronglyMeasurable
  have hg_int : Integrable g (geometricMeasure p) :=
    hω_int.mono hg_meas (ae_of_all _ (fun k => hdom ω hωA k))
  have hpbool : p != 0 := by
    simpa using hp
  exact (AvramDividend.Classical.avram_a19_singular_geometric_not_integrable
    p hpbool hhalf y hy hsmall hpower) (by simpa [g] using hg_int)
