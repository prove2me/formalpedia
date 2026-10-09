-- Prove2me | solution 1 for BookProof.ChapterA3.chargeConj_mgamma_commutes
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:03:40.62793+00:00
-- url     : https://prove2.me/submissions/ab210d85-90d3-4022-b53f-1f7c25f5f32a

-- Generated from ChapterA3b.lean — solution of BookProof.ChapterA3.chargeConj_mgamma_commutes
import Mathlib
import Definitions.Def_ChapterA3b
import Theorems.Thm_BookProof_ChapterA3_mgamma_map_conj
open BookProof.ChapterA3



open Matrix
open scoped ComplexConjugate

set_option maxHeartbeats 1000000 in
theorem solution (μ : Fin 4) (v : Fin 4 → ℂ) :
    chargeConj (mgamma μ *ᵥ v) = mgamma μ *ᵥ chargeConj v := by

  funext i
  simp only [chargeConj, mulVec, dotProduct, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul]
  congr 1
  have := congrFun (congrFun (mgamma_map_conj μ) i) j
  simpa [Matrix.map_apply] using this
