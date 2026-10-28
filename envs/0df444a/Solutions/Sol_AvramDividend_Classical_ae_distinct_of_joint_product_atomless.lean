-- Prove2me | solution 1 for AvramDividend.Classical.ae_distinct_of_joint_product_atomless
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:09:54.43086+00:00
-- url     : https://prove2.me/submissions/44cb5f36-bc01-4ae9-9daa-3ff870e01793

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Probability.IdentDistrib

open MeasureTheory
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U V : Ω → ℝ)
    (hUV : Measurable (fun ω => (U ω, V ω)))
    (μ ν : Measure ℝ) [SFinite ν] [NullSingletonClass ν]
    (hjoint : P.map (fun ω => (U ω, V ω)) = μ.prod ν) :
    ∀ᵐ ω ∂P, U ω ≠ V ω := by
  have hs : MeasurableSet {p : ℝ × ℝ | p.1 = p.2} := measurableSet_diagonal
  have h0 : μ.prod ν {p : ℝ × ℝ | p.1 = p.2} = 0 := by
    rw [Measure.prod_apply hs]
    have : ∀ x : ℝ, ν (Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1 = p.2}) = 0 := by
      intro x
      have : Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1 = p.2} = {x} := by
        ext y; simp [eq_comm]
      rw [this]; exact measure_singleton x
    simp [this]
  rw [ae_iff]
  simp only [ne_eq, not_not]
  rw [← hjoint, Measure.map_apply hUV hs] at h0
  exact h0
