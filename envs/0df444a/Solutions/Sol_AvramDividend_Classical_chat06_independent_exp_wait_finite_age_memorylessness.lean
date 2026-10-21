-- Prove2me | solution 1 for AvramDividend.Classical.chat06_independent_exp_wait_finite_age_memorylessness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T20:11:22.067374+00:00
-- url     : https://prove2.me/submissions/c4d4f79c-b4af-4f17-91f0-adb042cda943

import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Theorems.Thm_AvramDividend_Classical_chat06_independent_exp_wait_atom_memorylessness

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace AvramChat06

/-- Finite-valued random-age memorylessness, proved using the
accepted fixed-atom factorisation plus a finite disjoint union.
The next phase must remove finite range by approximation and
measure convergence for arbitrary continuous observed ages. -/
theorem independent_exp_wait_finite_valued_age_survival
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A τ : Ω → ℝ)
    (hA : Measurable A) (hτ : Measurable τ)
    (hInd : IndepFun A τ P)
    (hTail : ∀ u : ℝ, 0 ≤ u →
      P {ω | u < τ ω} = ENNReal.ofReal (Real.exp (-u)))
    (S : Finset ℝ) (hRange : ∀ ω, A ω ∈ S)
    (hNonneg : ∀ a ∈ S, 0 ≤ a)
    (t : ℝ) (ht : 0 ≤ t) :
    P {ω | A ω + t < τ ω} =
      P {ω | A ω < τ ω} *
        ENNReal.ofReal (Real.exp (-t)) := by
  let F : ℝ → Set Ω := fun a =>
    {ω | A ω = a ∧ a + t < τ ω}
  let G : ℝ → Set Ω := fun a =>
    {ω | A ω = a ∧ a < τ ω}
  have hFmeas (a : ℝ) : MeasurableSet (F a) := by
    change MeasurableSet ({ω | A ω = a} ∩ τ ⁻¹' Ioi (a + t))
    exact (hA (measurableSet_singleton a)).inter
      (hτ measurableSet_Ioi)
  have hGmeas (a : ℝ) : MeasurableSet (G a) := by
    change MeasurableSet ({ω | A ω = a} ∩ τ ⁻¹' Ioi a)
    exact (hA (measurableSet_singleton a)).inter
      (hτ measurableSet_Ioi)
  have hDis (u : ℝ) : PairwiseDisjoint (↑S)
      (fun a : ℝ => {ω | A ω = a ∧ a + u < τ ω}) := by
    intro a ha b hb hab
    apply Set.disjoint_left.mpr
    intro ω haω hbω
    exact hab (haω.1.symm.trans hbω.1)
  have hUnion (u : ℝ) :
      {ω | A ω + u < τ ω} =
      ⋃ a ∈ S, {ω | A ω = a ∧ a + u < τ ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro h
      exact ⟨A ω, hRange ω, rfl, h⟩
    · rintro ⟨a, ha, hEq, h⟩
      simpa [hEq] using h
  have hL : P {ω | A ω + t < τ ω} =
      ∑ a ∈ S, P (F a) := by
    rw [hUnion t]
    exact measure_biUnion_finset (hDis t)
      (fun a ha => hFmeas a)
  have hR : P {ω | A ω < τ ω} =
      ∑ a ∈ S, P (G a) := by
    have h0 : {ω | A ω < τ ω} =
        {ω | A ω + (0 : ℝ) < τ ω} := by simp
    rw [h0, hUnion 0]
    simpa only [add_zero, G] using
      (measure_biUnion_finset (hDis 0)
        (fun a ha => by simpa only [add_zero, G] using hGmeas a))
  have hAtom (a : ℝ) (ha : a ∈ S) :
      P (F a) = P (G a) *
        ENNReal.ofReal (Real.exp (-t)) := by
    have h := AvramDividend.Classical.chat06_independent_exp_wait_atom_memorylessness
      P A τ hInd hTail a t (hNonneg a ha) ht
    change P ({ω | A ω = a} ∩ {ω | a + t < τ ω}) =
      P ({ω | A ω = a} ∩ {ω | a < τ ω}) *
        ENNReal.ofReal (Real.exp (-t))
    exact h
  rw [hL, hR]
  calc
    (∑ a ∈ S, P (F a)) =
        ∑ a ∈ S, (P (G a) * ENNReal.ofReal (Real.exp (-t))) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact hAtom a ha
    _ = (∑ a ∈ S, P (G a)) *
          ENNReal.ofReal (Real.exp (-t)) := by
      rw [Finset.sum_mul]

end AvramChat06

open AvramChat06

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A τ : Ω → ℝ)
    (hA : Measurable A) (hτ : Measurable τ)
    (hInd : IndepFun A τ P)
    (hTail : ∀ u : ℝ, 0 ≤ u →
      P {ω | u < τ ω} = ENNReal.ofReal (Real.exp (-u)))
    (S : Finset ℝ) (hRange : ∀ ω, A ω ∈ S)
    (hNonneg : ∀ a ∈ S, 0 ≤ a)
    (t : ℝ) (ht : 0 ≤ t) :
    P {ω | A ω + t < τ ω} =
      P {ω | A ω < τ ω} *
        ENNReal.ofReal (Real.exp (-t)) := by
  exact independent_exp_wait_finite_valued_age_survival
    P A τ hA hτ hInd hTail S hRange hNonneg t ht
