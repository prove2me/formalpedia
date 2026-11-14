-- Prove2me | solution 1 for ConsistentSubmodular.FiniteLaw.exists_good_positive_of_sum_failure_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:29:32.158964+00:00
-- url     : https://prove2.me/submissions/165fed9f-2ef3-40a4-85ee-9661f0b86159

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_FiniteProbability

section

open scoped BigOperators
open ConsistentSubmodular
open ConsistentSubmodular.FiniteLaw
variable {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)

theorem solution {κ : Type*} [Fintype κ]
    (bad : κ → Ω → Prop) (hbad : (∑ i, μ.probability (bad i)) < 1) :
    ∃ ω, 0 < μ.weight ω ∧ ∀ i, ¬bad i ω := by
  classical
  by_contra h
  push Not at h
  have hpoint (ω : Ω) : μ.weight ω ≤ ∑ i, if bad i ω then μ.weight ω else 0 := by
    by_cases hw : 0 < μ.weight ω
    · obtain ⟨i, hi⟩ := h ω hw
      have hs := Finset.single_le_sum (s := Finset.univ)
        (f := fun i => if bad i ω then μ.weight ω else 0)
        (fun i _ => by split_ifs; exact μ.nonnegative ω; rfl) (Finset.mem_univ i)
      simpa only [hi, ite_true] using hs
    · have hz : μ.weight ω = 0 := le_antisymm (le_of_not_gt hw) (μ.nonnegative ω)
      simp [hz]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun ω _ => hpoint ω)
  rw [μ.sum_one, Finset.sum_comm] at hs
  exact (not_lt_of_ge hs) hbad

end
