-- Prove2me | solution 1 for BitDFT.fixed_point_multiplication
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T01:30:18.350709+00:00
-- url     : https://prove2.me/submissions/42d512b6-031e-4c16-b0c8-4e1b7b89bb0e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BitDFT_fixed_point_multiplication_machine
import Theorems.Thm_BitDFT_fixed_point_product_error
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
          W = roundPair p (value p U * value p V) ∧ inDisc p W ∧
          ∀ u v : ℂ, ‖u‖ ≤ 1 → ‖v‖ ≤ 1 →
            ulpError p W (u * v) < ulpError p U u + ulpError p V v + 2 := by
  obtain ⟨A, C, hC, hA⟩ := BitDFT.fixed_point_multiplication_machine M T hM
  refine ⟨A, C, hC, ?_⟩
  intro p hp U V hU hV
  obtain ⟨W, hcomp, hW, hdisc⟩ := hA p hp U V hU hV
  refine ⟨W, hcomp, hW, hdisc, ?_⟩
  intro u v hu hv
  rw [hW]
  exact BitDFT.fixed_point_product_error p U V hU hV u v hu hv
