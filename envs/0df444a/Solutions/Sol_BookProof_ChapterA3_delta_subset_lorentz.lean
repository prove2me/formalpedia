-- Prove2me | solution 1 for BookProof.ChapterA3.delta_subset_lorentz
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T16:21:31.182687+00:00
-- url     : https://prove2.me/submissions/9fe8552b-0803-4550-a9c6-ac86e257309e

import Mathlib
import Definitions.Def_ChapterA3d
import Definitions.Def_ChapterA3b
import Definitions.Def_ChapterA3c
import Definitions.Def_ChapterA3

open BookProof.ChapterA3
open Matrix

theorem solution : LorentzDelta ⊆ LorentzO := by
  intro Λ hΛ
  simp only [LorentzDelta, Set.mem_insert_iff, Set.mem_singleton_iff] at hΛ
  rcases hΛ with hΛ | hΛ | hΛ | hΛ
  · subst Λ
    simp [LorentzO]
  · subst Λ
    have hsym : minkowskiMatᵀ = minkowskiMat := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [minkowskiMat, minkowskiR, minkowskiZ]
    have hsq : minkowskiMat * minkowskiMat = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [minkowskiMat, minkowskiR, minkowskiZ, Matrix.mul_apply]
    change minkowskiMat * minkowskiMat * minkowskiMatᵀ = minkowskiMat
    rw [hsym, hsq, one_mul]
  · subst Λ
    have hsym : minkowskiMatᵀ = minkowskiMat := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [minkowskiMat, minkowskiR, minkowskiZ]
    have hsq : minkowskiMat * minkowskiMat = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [minkowskiMat, minkowskiR, minkowskiZ, Matrix.mul_apply]
    simp [LorentzO, hsym, hsq]
  · subst Λ
    simp [LorentzO]

#print axioms solution
