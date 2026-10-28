-- Prove2me | solution 1 for BitDFT.encVector_prefix_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T00:57:29.223001+00:00
-- url     : https://prove2.me/submissions/1f7621d8-fe49-4710-af8d-96fd6ca61abf

import Definitions.Def_BitDFT_Encoding
import Mathlib.Data.List.OfFn

set_option autoImplicit false
open BitDFT IntMul

theorem solution {n : ℕ} (w j : ℕ) (U : Fin n → ℤ × ℤ) :
    encVector w U =
      ((List.finRange n).take j).flatMap (fun i => encComplex w (U i)) ++
      ((List.finRange n).drop j).flatMap (fun i => encComplex w (U i)) := by
  change List.flatMap (fun i => encComplex w (U i)) (List.finRange n) = _
  have hsplit := congrArg (List.flatMap (fun i => encComplex w (U i)))
    (List.take_append_drop j (List.finRange n)).symm
  calc
    _ = List.flatMap (fun i => encComplex w (U i))
        ((List.finRange n).take j ++ (List.finRange n).drop j) := hsplit
    _ = _ := List.flatMap_append
