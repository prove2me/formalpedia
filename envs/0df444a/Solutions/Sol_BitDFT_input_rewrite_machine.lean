-- Prove2me | solution 1 for BitDFT.input_rewrite_machine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T17:43:26.86576+00:00
-- url     : https://prove2.me/submissions/69b126e7-b9c0-46ca-8735-994bad7f13c9

import Theorems.Thm_BitDFT_native_child_output_correct
import Theorems.Thm_BitDFT_multiplier_time_linear
import Mathlib.Tactic.Linarith

noncomputable section
open BitDFT IntMul

theorem solution (M : MultitapeTM) (T : ℕ → ℝ) (hM : Multiplier M T)
    (A : MultitapeTM) (C : ℝ) (hC : 0 < C) :
    ∃ B : MultitapeTM, ∃ D : ℝ, 0 < D ∧
      ∀ n b : ℕ, 1 ≤ n → 1 ≤ b → ∀ U : Fin n → ℤ × ℤ, ∀ w : List Bool,
        Computes A (fourierInput (guardPrecision n b) U) w (C*transferCost T n (guardPrecision n b)) →
        Computes B (requestedInput b U) w (D*transferCost T n (guardPrecision n b)) := by
  refine ⟨NativeChildOutput.program A,181+10*C,by linarith,?_⟩
  intro n b hn hb U w hrun
  let q := guardPrecision n b
  have hq : 1 ≤ q := by unfold q guardPrecision; omega
  have hnq : 1 ≤ n*q := by nlinarith
  have hTq := BitDFT.multiplier_time_linear M q (T q) (hM q hq)
  have hTnq := BitDFT.multiplier_time_linear M (n*q) (T (n*q)) (hM (n*q) hnq)
  have hTq0 : 0 ≤ T q := (Nat.cast_nonneg (2*q)).trans hTq
  have hTnq0 : 0 ≤ T (n*q) := (Nat.cast_nonneg (2*(n*q))).trans hTnq
  have hlinear : (n:ℝ)*q ≤ transferCost T n q := by
    unfold transferCost
    have h1 := mul_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n) hTq0
    have h2 := mul_nonneg (Nat.cast_nonneg q : (0:ℝ) ≤ q) (sq_nonneg (lg q : ℝ))
    linarith
  obtain ⟨s,hs,hhalt⟩ := hrun
  obtain ⟨t,v,ht,_,hout,_⟩ := BitDFT.native_child_output_correct A n b hn hb U s hhalt.1 w hhalt.2
  refine ⟨t,?_,hout⟩
  have htR : (t:ℝ) ≤ 181*(n:ℝ)*q+10*s := by exact_mod_cast ht
  change (s:ℝ) ≤ C*transferCost T n q at hs
  change (t:ℝ) ≤ (181+10*C)*transferCost T n q
  nlinarith
