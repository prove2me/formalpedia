-- Prove2me | solution 1 for BitDFT.encVector_as_signed_list
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T02:27:46.676996+00:00
-- url     : https://prove2.me/submissions/d7ab0431-c6fb-4e8d-b970-bf2d31f81043

import Definitions.Def_BitDFT_Encoding

set_option autoImplicit false
open BitDFT

/-- The native complex-vector tape is already a flat real/imaginary integer list. -/
theorem solution {n : ℕ} (w : ℕ) (U : Fin n → ℤ × ℤ) :
    encVector w U = encList w
      ((List.finRange n).flatMap (fun i : Fin n => [(U i).1, (U i).2])) ∧
    ((List.finRange n).flatMap (fun i : Fin n => [(U i).1, (U i).2])).length = 2*n := by
  constructor
  · simp [encVector, encComplex, encList, List.flatMap_assoc]
  · simp
    omega
