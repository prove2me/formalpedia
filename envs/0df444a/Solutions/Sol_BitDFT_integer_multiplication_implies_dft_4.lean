-- Prove2me | solution 4 for BitDFT.integer_multiplication_implies_dft
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T14:53:42.965504+00:00
-- url     : https://prove2.me/submissions/6a8dbf48-9866-4087-baa4-6bb2208d503f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BitDFT_dft_machine_explicit_overhead
import Theorems.Thm_BitDFT_rescale_output_machine
import Theorems.Thm_BitDFT_guarded_output_correct
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
            (∀ k, ‖value (guardPrecision n b) (V k) -
              dft (fun j => value (guardPrecision n b) (U j)) k‖ < ((2 : ℝ) ^ b)⁻¹) := by
  obtain ⟨A, C, hC, hA⟩ := BitDFT.dft_machine_explicit_overhead M T hM
  obtain ⟨B, D, hD, hB⟩ := BitDFT.rescale_output_machine M T hM A C hC
  refine ⟨B, D, hD, ?_⟩
  intro n b hn hb U hU
  have hq : 1 ≤ guardPrecision n b := by unfold guardPrecision; omega
  have hl : IntMul.lg n ≤ guardPrecision n b := by unfold guardPrecision; omega
  obtain ⟨W, ht, hd, he⟩ := hA n (guardPrecision n b) hn hq hl U hU
  have hzero : approx (guardPrecision n b) U
      (fun j => value (guardPrecision n b) (U j)) 0 := by
    intro j
    simp [ulpError]
  have hcorrect := BitDFT.guarded_output_correct n b hn
    (fun j => value (guardPrecision n b) (U j)) W hd
    (by simpa using he _ 0 hU hzero)
  exact ⟨(fun k => ((n : ℤ) * (W k).1, (n : ℤ) * (W k).2)),
    hB n b hn hb U W hU hd ht, hcorrect⟩
