-- Prove2me | solution 1 for BitDFT.clean_multiplier_call
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T13:35:18.528979+00:00
-- url     : https://prove2.me/submissions/10199873-5dae-4abd-b2ba-967de1388e65

import Theorems.Thm_IntMul_TrackedNativeCall_call_correct
import Theorems.Thm_BitDFT_output_length_le_time
import Definitions.Def_BitDFT_Encoding
set_option autoImplicit false
open IntMul
open IntMul.TrackedBankCleanup (span)
open IntMul.TrackedBankedSimulation (extents nextExtent)
open IntMul.TrackedBankPreparation (inputWord initialExtent)

private lemma clean_head_bound (M : MultitapeTM) (x y : List Bool) (t : ℕ) :
    ∀ i, (M.step^[t] (M.initCfg x y)).head i ≤ t := by
  induction t with
  | zero => simp [MultitapeTM.initCfg]
  | succ t ih =>
    intro i
    rw [Function.iterate_succ_apply']
    simp only [MultitapeTM.step]
    split <;> have hi := ih i <;> omega

private lemma clean_extent_bound (M : MultitapeTM) (x y : List Bool) (t : ℕ) :
    ∀ i, extents M (M.initCfg x y) (initialExtent M x y) t i ≤
      (inputWord M x y).length + t := by
  induction t with
  | zero =>
    intro i
    simp only [extents, initialExtent]
    split <;> omega
  | succ t ih =>
    intro i
    have he := ih i
    have hh := clean_head_bound M x y t i
    simp only [extents, nextExtent]
    split <;> (try simp only [max_le_iff]) <;> omega

private lemma clean_span_bound (M : MultitapeTM) (x y : List Bool) (t : ℕ) :
    span M (extents M (M.initCfg x y) (initialExtent M x y) t) ≤
      (inputWord M x y).length + t := by
  exact Finset.sup_le fun i _ => clean_extent_bound M x y t i

theorem solution (M : MultitapeTM) (s : ℕ) (T : ℝ)
    (hs : 1 ≤ s) (hM : MultipliesAt M s T) :
    ∀ x y : List Bool, x.length = s → y.length = s →
    ∃ t : ℕ, (t : ℝ) ≤ 36 * T ∧
      (IntMul.TrackedNativeCall.machine M).HaltsWithOutput x y t
        (IntMul.bin (2 * s) (IntMul.val x * IntMul.val y)) ∧
      (∀ j p, 1 ≤ p →
        ((IntMul.TrackedNativeCall.machine M).step^[t]
          ((IntMul.TrackedNativeCall.machine M).initCfg x y)).cells
          (IntMul.BankedSimulation.workTape M j) p = some (M.blank, false)) ∧
      (∀ j, ((IntMul.TrackedNativeCall.machine M).step^[t]
        ((IntMul.TrackedNativeCall.machine M).initCfg x y)).head
          (IntMul.BankedSimulation.workTape M j) = 1) := by
  intro x y hx hy
  obtain ⟨t, ht, hout⟩ := hM x y hx hy
  have hl := BitDFT.output_length_le_time M x y
    (IntMul.bin (2 * s) (IntMul.val x * IntMul.val y)) t hout
  simp only [IntMul.bin, List.length_ofFn] at hl
  obtain ⟨u, hu, hout', hclear, hheads⟩ :=
    IntMul.TrackedNativeCall.call_correct M x y t hout.1 _ hout.2
  have he := clean_span_bound M x y t
  have hlen : (inputWord M x y).length = 2 * s + 1 := by
    simp [inputWord, hx, hy]; omega
  rw [hlen] at he hu
  simp only [IntMul.bin, List.length_ofFn] at hu
  have hub : u ≤ 36 * t := by omega
  have hubR : (u : ℝ) ≤ 36 * (t : ℝ) := by exact_mod_cast hub
  refine ⟨u, hubR.trans ?_, hout', hclear, hheads⟩
  exact mul_le_mul_of_nonneg_left ht (by norm_num)
