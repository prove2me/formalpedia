-- Prove2me | solution 2 for BitDFT.integer_multiplication_implies_dft_input_error
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T12:39:46.802997+00:00
-- url     : https://prove2.me/submissions/3b7d7eaa-4d4d-4748-917b-ea9350cc738e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_BitDFT_Numerics
import Definitions.Def_IntMul_HvdH_KronMul
import Theorems.Thm_BitDFT_integer_multiplication_implies_dft
import Theorems.Thm_BitDFT_dft_stability
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open BitDFT

theorem solution
    (M : IntMul.MultitapeTM) (T : ℕ → ℝ) (hM : Multiplier M T) :
    ∃ A : IntMul.MultitapeTM, ∃ C : ℝ, 0 < C ∧
      ∀ n b : ℕ, 1 ≤ n → 1 ≤ b →
        ∀ U : Fin n → ℤ × ℤ, vectorDisc (guardPrecision n b) U →
          ∃ V : Fin n → ℤ × ℤ,
            Computes A (requestedInput b U)
              (encVector (guardPrecision n b + IntMul.lg n + 1) V)
              (C * transferCost T n (guardPrecision n b)) ∧
            (∀ k, ‖value (guardPrecision n b) (V k)‖ ≤ n) ∧
            ∀ (X : Fin n → ℂ) (δ : ℝ),
              (∀ j, ‖value (guardPrecision n b) (U j) - X j‖ ≤ δ) →
              ∀ k, ‖value (guardPrecision n b) (V k) - dft X k‖ <
                (n : ℝ) * δ + ((2 : ℝ) ^ b)⁻¹ := by
  obtain ⟨A, C, hC, hA⟩ := BitDFT.integer_multiplication_implies_dft M T hM
  refine ⟨A, C, hC, fun n b hn hb U hU => ?_⟩
  obtain ⟨V, hc, h1, h2⟩ := hA n b hn hb U hU
  refine ⟨V, hc, h1, fun X δ hX k => ?_⟩
  have hs := BitDFT.dft_stability _ X δ hX k
  calc ‖value (guardPrecision n b) (V k) - dft X k‖
      ≤ ‖value (guardPrecision n b) (V k) - dft (fun j => value (guardPrecision n b) (U j)) k‖ +
        ‖dft (fun j => value (guardPrecision n b) (U j)) k - dft X k‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ((2 : ℝ) ^ b)⁻¹ + (n : ℝ) * δ := add_lt_add_of_lt_of_le (h2 k) hs
    _ = _ := add_comm _ _
