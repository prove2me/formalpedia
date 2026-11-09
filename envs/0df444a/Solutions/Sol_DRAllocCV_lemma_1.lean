-- Prove2me | solution 1 for DRAllocCV.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T11:52:19.389192+00:00
-- url     : https://prove2.me/submissions/c8acd420-86cd-4bba-8ba6-94b1c92e89d3

import Mathlib
import Definitions.Def_DRAllocCV_Feasible

open MeasureTheory

open DRAllocCV in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] (hI : 2 ≤ Fintype.card ι)
    (tlo thi c : ι → ℝ) (htlo : ∀ i, 0 ≤ tlo i) (htt : ∀ i, tlo i < thi i) (hc : ∀ i, 0 < c i)
    (p q : ι → (ι → ℝ) → ℝ) (hX : Feasible tlo thi p q) (i : ι) (t : ι → ℝ)
    (ht : t ∈ typeSpace tlo thi) :
    (p i t - q i t = 1 → ∀ s ∈ Set.Icc (tlo i) (thi i), p i (Function.update t i s) = 1) ∧
    (p i t = 0 → ∀ s ∈ Set.Icc (tlo i) (thi i),
      p i (Function.update t i s) = q i (Function.update t i s)) := by
  obtain ⟨-, hbd, hqp, hic⟩ := hX
  have hmem : ∀ s ∈ Set.Icc (tlo i) (thi i), Function.update t i s ∈ typeSpace tlo thi := by
    intro s hs
    unfold typeSpace
    rw [Set.mem_univ_pi]
    intro j
    by_cases hj : j = i
    · subst hj; simpa using hs
    · rw [Function.update_of_ne hj]
      unfold typeSpace at ht
      exact (Set.mem_univ_pi.mp ht) j
  have hti : t i ∈ Set.Icc (tlo i) (thi i) := by
    unfold typeSpace at ht
    exact (Set.mem_univ_pi.mp ht) i
  constructor
  · intro h1 s hs
    have h := hic i (Function.update t i s) (hmem s hs) (t i) hti
    rw [Function.update_idem, Function.update_eq_self] at h
    have hle := (hbd _ (hmem s hs) i).2.1
    linarith
  · intro h0 s hs
    have h := hic i t ht s hs
    have hq := (hqp _ (hmem s hs)).1 i
    linarith
