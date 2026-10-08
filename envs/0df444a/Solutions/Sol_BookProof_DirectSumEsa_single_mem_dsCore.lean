-- Prove2me | solution 1 for BookProof.DirectSumEsa.single_mem_dsCore
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T10:37:12.287367+00:00
-- url     : https://prove2.me/submissions/29f5580d-27c0-4fcc-8b05-909af195afc5

-- Generated from ChapterDirectSumEsa.lean — solution of BookProof.DirectSumEsa.single_mem_dsCore
import Mathlib
import Definitions.Def_ChapterDirectSumEsa
open BookProof.DirectSumEsa



open scoped ENNReal


open BookProof.FarisLavine

noncomputable section

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)]

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)]
variable {D : ∀ i, Submodule ℂ (G i)}

set_option maxHeartbeats 1000000 in
theorem solution [DecidableEq ι] (i : ι) (u : D i) :
    (lp.single 2 i ((u : G i)) : lp G 2) ∈ dsCore D := by

  classical
  constructor
  · refine Set.Finite.subset (Set.finite_singleton i) (fun j hj => ?_)
    simp only [Set.mem_setOf_eq, lp.single_apply] at hj
    by_contra hne
    exact hj (Pi.single_eq_of_ne (by simpa [eq_comm] using hne) _)
  · intro j
    rw [lp.single_apply]
    by_cases hj : j = i
    · subst hj
      simp only [Pi.single_eq_same]
      exact u.2
    · rw [Pi.single_eq_of_ne (by simpa [eq_comm] using hj)]
      exact Submodule.zero_mem _
