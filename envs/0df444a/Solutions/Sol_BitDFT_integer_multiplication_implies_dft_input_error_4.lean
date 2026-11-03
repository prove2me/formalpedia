-- Prove2me | solution 4 for BitDFT.integer_multiplication_implies_dft_input_error
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-02T15:39:48.109196+00:00
-- url     : https://prove2.me/submissions/1d174520-844e-4c54-ba5f-6b396c6a432e
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
  obtain ⟨A, C, hC, h⟩ := BitDFT.integer_multiplication_implies_dft M T hM
  refine ⟨A, C, hC, ?_⟩
  intro n b hn hb U hU
  obtain ⟨V, hcomp, h1, h2⟩ := h n b hn hb U hU
  refine ⟨V, hcomp, h1, ?_⟩
  intro X δ hX k
  have hstab := BitDFT.dft_stability (fun j => value (guardPrecision n b) (U j)) X δ hX k
  have hsplit : value (guardPrecision n b) (V k) - dft X k =
      (value (guardPrecision n b) (V k) -
        dft (fun j => value (guardPrecision n b) (U j)) k) +
      (dft (fun j => value (guardPrecision n b) (U j)) k - dft X k) := by
    ring
  rw [hsplit]
  have htri := norm_add_le
    (value (guardPrecision n b) (V k) -
      dft (fun j => value (guardPrecision n b) (U j)) k)
    (dft (fun j => value (guardPrecision n b) (U j)) k - dft X k)
  have hmain := h2 k
  linarith
