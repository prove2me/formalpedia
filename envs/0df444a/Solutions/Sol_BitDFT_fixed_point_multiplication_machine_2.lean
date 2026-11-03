-- Prove2me | solution 2 for BitDFT.fixed_point_multiplication_machine
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-02T15:39:31.843905+00:00
-- url     : https://prove2.me/submissions/a5dcf615-2fcd-4038-a205-4efc1f3b58c6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_BitDFT_Numerics
import Definitions.Def_IntMul_HvdH_KronMul
import Theorems.Thm_BitDFT_fixed_point_multiplication_machine_core
import Theorems.Thm_BitDFT_roundPair_product_disc
set_option autoImplicit false
noncomputable section
open BitDFT

theorem solution (M : IntMul.MultitapeTM) (T : ℕ → ℝ)
    (hM : Multiplier M T) :
    ∃ A : IntMul.MultitapeTM, ∃ C : ℝ, 0 < C ∧
      ∀ (p : ℕ), 1 ≤ p → ∀ U V : ℤ × ℤ, inDisc p U → inDisc p V →
        ∃ W : ℤ × ℤ,
          Computes A (encNat p ++ encComplex (p + 1) U ++ encComplex (p + 1) V)
            (encComplex (p + 1) W) (C * T p) ∧
          W = roundPair p (value p U * value p V) ∧ inDisc p W := by
  obtain ⟨A, C, hC, h⟩ :=
    BitDFT.fixed_point_multiplication_machine_core M T hM
  refine ⟨A, C, hC, ?_⟩
  intro p hp U V hU hV
  obtain ⟨W, hcomp, hW⟩ := h p hp U V hU hV
  refine ⟨W, hcomp, hW, ?_⟩
  rw [hW]
  exact BitDFT.roundPair_product_disc p U V hU hV
