-- Prove2me | solution 3 for BitDFT.integer_multiplication_implies_dft
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T13:37:30.413919+00:00
-- url     : https://prove2.me/submissions/adc0fade-e3f5-433e-8446-ae0077fd72c8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BitDFT_clean_multiplier_call
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
  let N := IntMul.TrackedNativeCall.machine M
  let S : ℕ → ℝ := fun s => 36 * T s
  have hN : Multiplier N S := by
    intro s hs x y hx hy
    obtain ⟨t, ht, ho, _⟩ := BitDFT.clean_multiplier_call M s (T s) hs (hM s hs) x y hx hy
    exact ⟨t, ht, ho⟩
  obtain ⟨A, C, hC, hA⟩ := BitDFT.dft_machine_explicit_overhead N S hN
  obtain ⟨B, D, hD, hB⟩ := BitDFT.rescale_output_machine N S hN A C hC
  refine ⟨B, 36 * D, mul_pos (by norm_num) hD, ?_⟩
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
  have hrun := hB n b hn hb U W hU hd ht
  have hcost : transferCost S n (guardPrecision n b) ≤
      36 * transferCost T n (guardPrecision n b) := by
    have hsetup : 0 ≤ (guardPrecision n b : ℝ) *
        (IntMul.lg (guardPrecision n b) : ℝ)^2 :=
      mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    have hio : 0 ≤ (n : ℝ) * (guardPrecision n b : ℝ) :=
      mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    dsimp [transferCost, S]
    nlinarith
  obtain ⟨t, ht', hout⟩ := hrun
  refine ⟨(fun k => ((n : ℤ) * (W k).1, (n : ℤ) * (W k).2)),
    ⟨t, ?_, hout⟩, hcorrect⟩
  calc
    (t : ℝ) ≤ D * transferCost S n (guardPrecision n b) := ht'
    _ ≤ D * (36 * transferCost T n (guardPrecision n b)) :=
      mul_le_mul_of_nonneg_left hcost hD.le
    _ = (36 * D) * transferCost T n (guardPrecision n b) := by ring
