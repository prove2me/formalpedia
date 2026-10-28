-- Prove2me | solution 1 for BitDFT.integer_multiplication_implies_dft_input_error
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T12:28:58.332232+00:00
-- url     : https://prove2.me/submissions/88a090a7-1456-4a02-8c1d-18a411208c76
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

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
  refine ⟨A, C, hC, ?_⟩
  intro n b hn hb U hU
  obtain ⟨V, ht, hd, he⟩ := hA n b hn hb U hU
  refine ⟨V, ht, hd, ?_⟩
  intro X δ hX k
  have hs := BitDFT.dft_stability (fun j => value (guardPrecision n b) (U j)) X δ hX k
  have htri := dist_triangle (value (guardPrecision n b) (V k))
    (dft (fun j => value (guardPrecision n b) (U j)) k) (dft X k)
  simp only [dist_eq_norm] at htri
  linarith only [htri, hs, he k]
