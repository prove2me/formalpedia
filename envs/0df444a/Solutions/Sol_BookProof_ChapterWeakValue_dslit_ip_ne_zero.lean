-- Prove2me | solution 1 for BookProof.ChapterWeakValue.dslit_ip_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T12:44:15.778944+00:00
-- url     : https://prove2.me/submissions/19913e71-597b-4e2e-86ab-1703dd524884

-- Generated from ChapterWeakValue.lean — theorem BookProof.ChapterWeakValue.dslit_ip_ne_zero
import Mathlib
import Definitions.Def_ChapterWeakValue
import Definitions.Def_ChapterDoubleSlit
open BookProof.ChapterDoubleSlit
open BookProof.ChapterWeakValue


open scoped BigOperators Matrix


variable {n : ℕ}
open BookProof.ChapterWeakValue

theorem solution: ip psi0 (H *ᵥ psi0) ≠ 0 := by
  simp [ip, H, psi0, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
