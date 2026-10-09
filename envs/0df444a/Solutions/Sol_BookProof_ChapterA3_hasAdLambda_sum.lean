-- Prove2me | solution 1 for BookProof.ChapterA3.hasAdLambda_sum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:07:30.359411+00:00
-- url     : https://prove2.me/submissions/da0f3ea6-3f2c-41fa-89bb-7afa35467184

-- Generated from ChapterA3e.lean — solution of BookProof.ChapterA3.hasAdLambda_sum
import Mathlib
import Definitions.Def_ChapterA3e
import Theorems.Thm_BookProof_ChapterA3_hasAdLambda_add
import Theorems.Thm_BookProof_ChapterA3_hasAdLambda_zero
open BookProof.ChapterA3



open Matrix

set_option maxHeartbeats 1000000 in
theorem solution {ι : Type*} (s : Finset ι)
    (G A : ι → Matrix (Fin 4) (Fin 4) ℝ) (h : ∀ i ∈ s, HasAdLambda (G i) (A i)) :
    HasAdLambda (∑ i ∈ s, G i) (∑ i ∈ s, A i) := by

  classical
  induction s using Finset.induction with
  | empty => simpa using hasAdLambda_zero
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact hasAdLambda_add (h i (Finset.mem_insert_self i s))
        (ih fun k hk => h k (Finset.mem_insert_of_mem hk))
