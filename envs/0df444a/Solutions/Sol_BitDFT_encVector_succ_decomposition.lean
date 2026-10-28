-- Prove2me | solution 1 for BitDFT.encVector_succ_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T00:48:49.652991+00:00
-- url     : https://prove2.me/submissions/33446d09-7bc7-40ea-9428-ea5488e7beac

import Definitions.Def_BitDFT_Encoding
import Mathlib.Data.List.OfFn

set_option autoImplicit false
open BitDFT IntMul

theorem solution {n : ℕ} (w : ℕ) (U : Fin (n + 1) → ℤ × ℤ) :
    encVector w U = encComplex w (U 0) ++
      encVector w (fun i : Fin n => U i.succ) := by
  simp [encVector, List.finRange_succ, List.flatMap_map]
