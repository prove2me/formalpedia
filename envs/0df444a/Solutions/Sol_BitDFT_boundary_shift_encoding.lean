-- Prove2me | solution 1 for BitDFT.boundary_shift_encoding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T20:39:55.466158+00:00
-- url     : https://prove2.me/submissions/fdf075cb-511e-4d58-b3b9-3d57235fd973

import Definitions.Def_IntMul_MultitapeModel
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bitwise

set_option autoImplicit false
open IntMul

private theorem bin_succ_shift (k z : ℕ) :
    bin (k+1) z = bin k (z/2) ++ [z.testBit 0] := by
  unfold bin
  rw [List.ofFn_succ', List.concat_eq_append]
  congr 1
  · congr 1
    funext i
    rw [Nat.testBit_div_two]
    congr 1
    simp only [Fin.val_castSucc]
    omega
  · simp

theorem solution (w n q : ℕ) :
    bin (w+q) (n*2^q) = bin w n ++ List.replicate q false := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [show w + (q+1) = (w+q)+1 by omega, bin_succ_shift]
      have hdiv : n * 2^(q+1) / 2 = n * 2^q := by
        rw [pow_succ]
        calc
          n * (2^q * 2) / 2 = (n * 2^q) * 2 / 2 := by rw [Nat.mul_assoc]
          _ = n * 2^q := by
            rw [Nat.mul_comm (n * 2^q) 2]
            exact Nat.mul_div_right (n * 2^q) (by decide : 0 < 2)
      have hdouble : n * 2^(q+1) = 2 * (n * 2^q) := by
        rw [pow_succ]
        ring
      have hbit : (n * 2^(q+1)).testBit 0 = false := by
        rw [hdouble, Nat.testBit_eq_decide_div_mod_eq]
        simp
      have hrepl : List.replicate q false ++ [false] = List.replicate (q+1) false := by
        simpa using (List.replicate_add q 1 false).symm
      rw [hdiv, hbit, ih]
      rw [List.append_assoc, hrepl]
