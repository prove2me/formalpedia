-- Prove2me | solution 1 for BitDFT.fixed_point_multiplication_machine
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T01:39:29.799267+00:00
-- url     : https://prove2.me/submissions/31f4f96c-86a0-452c-a0bf-4397ca27d5e4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BitDFT_fixed_point_multiplication_machine_core
import Theorems.Thm_BitDFT_roundPair_product_disc
import Definitions.Def_BitDFT_Numerics
import Definitions.Def_IntMul_HvdH_KronMul
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
  obtain ⟨A, C, hC, hA⟩ := BitDFT.fixed_point_multiplication_machine_core M T hM
  refine ⟨A, C, hC, ?_⟩
  intro p hp U V hU hV
  obtain ⟨W, hcomp, hW⟩ := hA p hp U V hU hV
  refine ⟨W, hcomp, hW, ?_⟩
  rw [hW]
  exact BitDFT.roundPair_product_disc p U V hU hV
