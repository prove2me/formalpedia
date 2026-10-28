-- Prove2me | solution 2 for BitDFT.integer_multiplication_implies_dft
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T12:39:34.059848+00:00
-- url     : https://prove2.me/submissions/f318ea8a-4411-4f45-b85e-cec6b2af8410
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_BitDFT_Numerics
import Definitions.Def_IntMul_HvdH_KronMul
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
  refine ⟨B, D, hD, fun n b hn hb U hU => ?_⟩
  set p := guardPrecision n b with hp
  have hp1 : 1 ≤ p := by simp [hp, guardPrecision]
  have hlg : IntMul.lg n ≤ p := by simp only [hp, guardPrecision]; omega
  obtain ⟨W, hcomp, hWd, herr⟩ := hA n p hn hp1 hlg U hU
  have hX : ∀ j, ‖value p (U j)‖ ≤ 1 := fun j => hU j
  have happ : approx p U (fun j => value p (U j)) 0 := fun j => by simp [ulpError]
  have herr' : ∀ k, ulpError p (W k) (ndft (fun j => value p (U j)) k) < 12 * (n : ℝ) ^ 2 := by
    intro k; have := herr _ 0 hX happ k; simpa using this
  obtain ⟨h1, h2⟩ := BitDFT.guarded_output_correct n b hn _ W hWd herr'
  refine ⟨fun k => ((n : ℤ) * (W k).1, (n : ℤ) * (W k).2), ?_, h1, h2⟩
  exact hB n b hn hb U W hU hWd hcomp
