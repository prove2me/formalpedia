-- Prove2me | solution 1 for BookProof.ChapterSoftmaxBorn.coherentBorn_temperature_half
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T17:20:09.46527+00:00
-- url     : https://prove2.me/submissions/2b0b88be-eb31-4c38-8e79-10a9e1e4dc44

-- Generated from ChapterSoftmaxBorn.lean — solution of BookProof.ChapterSoftmaxBorn.coherentBorn_temperature_half
import Mathlib
import Definitions.Def_ChapterSoftmaxBorn
import Theorems.Thm_BookProof_ChapterSoftmaxBorn_coherentBorn_eq_softmax
import Definitions.Def_ChapterCoherentOverlap
open BookProof.ChapterSoftmaxBorn



open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlap

variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (q : EuclideanSpace ℝ (Fin n))
    (k : Fin m → EuclideanSpace ℝ (Fin n)) (r : ℝ) (hk : ∀ l, ‖k l‖ = r) (j : Fin m) :
    bornWeight q k j =
      Real.exp (inner ℝ q (k j) / (1 / 2)) / ∑ l, Real.exp (inner ℝ q (k l) / (1 / 2)) := by

  have hx : ∀ x : ℝ, x / (1 / 2) = 2 * x := fun x => by ring
  rw [coherentBorn_eq_softmax q k r hk j, softmax]
  simp only [hx]
