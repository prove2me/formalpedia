-- Prove2me | solution 1 for BookProof.QgOuterFock.sum_single_block
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T05:04:21.373777+00:00
-- url     : https://prove2.me/submissions/320ee97e-ef80-4f8a-a70c-72fc323feb95

import Mathlib
import Definitions.Def_ChapterQgOuterFockEsa
open BookProof.QgOuterFock
open Finset MvPolynomial

theorem solution {n : ℕ} (p : Fin n) (c : Fin 84) :
    ∑ i : Fin 84, ((if i = c then (1 : ℝ) else 0 : ℝ) : ℂ)
        • (X (pcoord p i) : MvPolynomial (Fin (n * 84)) ℂ) = X (pcoord p c) := by
  simp [sum_ite_eq', one_smul]
