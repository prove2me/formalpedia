-- Prove2me | solution 1 for EReal.coe_finset_sum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T00:31:18.42106+00:00
-- url     : https://prove2.me/submissions/fb6f32ca-4d84-4d5e-8a03-242767866aac

import Mathlib

open Finset

-- carved verbatim out of submission 28498841-88d3-4588-8338-6c8af1fdca7b, lines 12-18


theorem solution {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : EReal) = ∑ i ∈ s, (f i : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, EReal.coe_add, ih]
