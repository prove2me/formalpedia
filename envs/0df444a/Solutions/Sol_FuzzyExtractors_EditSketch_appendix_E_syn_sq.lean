-- Prove2me | solution 1 for FuzzyExtractors.EditSketch.appendix_E_syn_sq
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T23:52:53.492114+00:00
-- url     : https://prove2.me/submissions/46a25a50-da84-484e-854a-63573c4b2e16

import Mathlib
import Definitions.Def_FuzzyExtractors_EditSketch_Basic
open FuzzyExtractors.EditSketch
theorem solution {K : Type} [Field K] [Fintype K] [CharP K 2]
    (w : Finset Kˣ) (i : ℕ) :
    syn (2 * i) w = syn i w ^ 2 := by
  classical
  unfold syn
  rw [sum_pow_char]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← pow_mul, Nat.mul_comm]
#print axioms solution
