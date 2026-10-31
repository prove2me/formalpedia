-- Prove2me | solution 1 for BookProof.ChapterUnboundedPosition.sum_single_mem_mulDomain
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T20:41:57.793778+00:00
-- url     : https://prove2.me/submissions/ff0686ff-bbd2-4ba9-99d7-976b5814ebc7

import Mathlib
import Definitions.Def_ChapterUnboundedPosition
import Definitions.Def_ChapterContinuityUnitaryInfinite
open BookProof.ChapterContinuityUnitaryInfinite
open BookProof.ChapterUnboundedPosition
open scoped ENNReal InnerProductSpace
open BookProof.ChapterContinuityUnitaryInfinite (L2Z)

theorem solution (f : ℤ → ℝ) (psi : L2Z) (s : Finset ℤ) :
    (∑ i ∈ s, lp.single 2 i ((psi : ℤ → ℂ) i)) ∈ mulDomain f := by
  rw [mulDomain]
  change Memℓp (fun k => (f k : ℂ) *
      ((∑ i ∈ s, lp.single 2 i ((psi : ℤ → ℂ) i) : L2Z) : ℤ → ℂ) k) 2
  let y : L2Z := ∑ i ∈ s, lp.single 2 i ((f i : ℂ) * (psi : ℤ → ℂ) i)
  have hfun :
      (fun k => (f k : ℂ) *
          ((∑ i ∈ s, lp.single 2 i ((psi : ℤ → ℂ) i) : L2Z) : ℤ → ℂ) k) = (y : ℤ → ℂ) := by
    ext k
    simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single, y, Pi.single_apply, Finset.mul_sum, mul_ite, mul_zero]
    refine Finset.sum_congr rfl ?_
    intro x _
    split_ifs with h
    · simp [h]
    · rfl
  rw [hfun]
  exact y.2
