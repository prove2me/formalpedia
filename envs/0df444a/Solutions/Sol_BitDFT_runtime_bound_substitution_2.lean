-- Prove2me | solution 2 for BitDFT.runtime_bound_substitution
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T12:39:56.78201+00:00
-- url     : https://prove2.me/submissions/0136100a-aad9-428b-ba17-20e61523a113
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_BitDFT_Numerics
import Definitions.Def_IntMul_HvdH_KronMul
import Theorems.Thm_BitDFT_integer_multiplication_implies_dft
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open BitDFT

theorem solution
    (M : IntMul.MultitapeTM) (T B : ℕ → ℝ) (hM : Multiplier M T)
    (hB : ∀ n, 1 ≤ n → T n ≤ B n) :
    ∃ A : IntMul.MultitapeTM, ∃ C : ℝ, 0 < C ∧
      ∀ n b : ℕ, 1 ≤ n → 1 ≤ b →
        ∀ U : Fin n → ℤ × ℤ, vectorDisc (guardPrecision n b) U →
          ∃ V : Fin n → ℤ × ℤ,
            Computes A (requestedInput b U)
              (encVector (guardPrecision n b + IntMul.lg n + 1) V)
              (C * transferCost B n (guardPrecision n b)) ∧
            (∀ k, ‖value (guardPrecision n b) (V k)‖ ≤ n) ∧
            (∀ k, ‖value (guardPrecision n b) (V k) -
              dft (fun j => value (guardPrecision n b) (U j)) k‖ < ((2 : ℝ) ^ b)⁻¹) := by
  have hMB : Multiplier M B := by
    intro n hn x y hx hy
    obtain ⟨t, ht, hh⟩ := hM n hn x y hx hy
    exact ⟨t, ht.trans (hB n hn), hh⟩
  exact BitDFT.integer_multiplication_implies_dft M B hMB
