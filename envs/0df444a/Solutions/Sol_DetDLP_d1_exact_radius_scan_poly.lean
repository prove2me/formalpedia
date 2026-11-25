-- Prove2me | solution 1 for DetDLP.d1_exact_radius_scan_poly
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T05:31:46.258146+00:00
-- url     : https://prove2.me/submissions/24664caf-66c0-4344-8b4f-974e40398e8a

import Definitions.Def_DetDLP_D1Radius

import Theorems.Thm_Groundwork_PolyT_div
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_PolyT_pow_unary
import Theorems.Thm_Groundwork_Unary_of_length
import Theorems.Thm_Groundwork_Unary_of_le
import Theorems.Thm_Groundwork_PolyT_filter
import Definitions.Def_DetDLP_W5_M6Sort
set_option autoImplicit false
namespace DetDLP.D1

/-- Compare against the rounded degree cutoff using only integer powers. -/
theorem ceil_nine_tenths_le (b k : ℕ) :
    ⌈(b:ℝ)^((9:ℝ)/10)⌉₊ ≤ k ↔ b^9 ≤ k^10 := by
  rw [Nat.ceil_le, ← pow_le_pow_iff_left₀ (by positivity) (Nat.cast_nonneg k) (by decide : 10 ≠ 0)]
  rw [← Real.rpow_mul_natCast (Nat.cast_nonneg b)]
  norm_num
  norm_cast

theorem radiusTest_correct (b deg j : ℕ) (hb : 2 ≤ b) (hj : 2 ≤ j) :
    radiusTest b deg j = true ↔ j ≤ radius b deg := by
  let q := max deg ⌈(b:ℝ)^((9:ℝ)/10)⌉₊
  have hbr : (1:ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
  have hp : 0 < (q:ℝ) := by
    have h1 := (Real.one_le_rpow hbr (by norm_num : (0:ℝ) ≤ 9/10)).trans (Nat.le_ceil _)
    have h2 : (⌈(b:ℝ)^((9:ℝ)/10)⌉₊ : ℝ) ≤ q := by exact_mod_cast le_max_right _ _
    linarith
  change decide _ = true ↔ j ≤ max 1 ⌊Real.logb 2 ((b:ℝ) / q)⌋₊
  rw [decide_eq_true_eq,le_max_iff,or_iff_right (by omega : ¬ j ≤ 1)]
  rw [Nat.le_floor_iff' (by omega), Real.le_logb_iff_rpow_le (by norm_num) (div_pos (by linarith) hp), Real.rpow_natCast, le_div_iff₀ hp]
  rw [← ceil_nine_tenths_le, ← max_le_iff]
  change q ≤ b / 2^j ↔ _
  rw [Nat.le_div_iff_mul_le (by positivity),mul_comm q]
  norm_cast


open Groundwork Groundwork.PolyT
attribute [local fun_prop] Groundwork.PolyT.snd Groundwork.PolyT.fst Groundwork.PolyT.const Groundwork.PolyT.comp Groundwork.PolyT.div Groundwork.PolyT.mul Groundwork.PolyT.length P2M_Groundwork_PolyT_id__1c5d0f44cc8f

private theorem pconstpow {α : Type} [Enc α] {f : α → ℕ} (h : PolyT f) (k : ℕ) : PolyT (fun x => f x ^ k) := by
  induction k with
  | zero => simpa using (Groundwork.PolyT.const (α:=α) (1:ℕ))
  | succ k ih => simpa [pow_succ] using Groundwork.PolyT.mul ih h

private theorem testP : PolyT (fun x : (ℕ × ℕ) × ℕ => scanTest x.1.1 x.1.2 x.2) := by
  let X := (ℕ × ℕ) × ℕ
  let b := fun x : X => x.1.1
  let t := fun x : X => min x.2 (b x).bits.length
  have hb : PolyT b := by dsimp [b]; fun_prop
  have hu := Unary.of_length (bits hb)
  have ht : Unary t := hu.of_le (by dsimp [t]; fun_prop) (fun _ => min_le_right ..)
  have hpow : PolyT (fun x : X => 2^t x) := pow_unary (const 2) ht
  have hd := Groundwork.PolyT.div hb hpow
  have h10 := pconstpow hd 10
  have h9 := pconstpow hb 9
  change PolyT (fun x : X => decide (x.2 = 1) || (decide (2 ≤ x.2) && (decide (x.1.2 ≤ b x / 2 ^ t x) && decide (b x ^ 9 ≤ (b x / 2 ^ t x)^10))))
  fun_prop

theorem radiusScan_poly : PolyT radiusScan := by
  have hun := Unary.of_length (P2M_Groundwork_PolyT_cons__3a60f43a3b86 (Groundwork.PolyT.const false) (bits (Groundwork.PolyT.fst (Groundwork.PolyT.id' (α:=ℕ × ℕ)))))
  apply Groundwork.PolyT.length
  exact Groundwork.PolyT.filter testP (Groundwork.PolyT.range hun)

theorem radiusScan_eq (b deg : ℕ) (hb : 2 ≤ b) : radiusScan (b,deg) = radius b deg := by
  let r := radius b deg
  have hr : 1 ≤ r := le_max_left ..
  have hl : r ≤ b.bits.length := by
    by_contra! h
    have hs : 2 ≤ b.bits.length+1 := by rw [Nat.size_eq_bits_len]; have := Nat.size_pos.mpr (by omega : 0<b); omega
    have ht := (radiusTest_correct b deg (b.bits.length+1) hb hs).mpr (by omega)
    have hdiv : b / 2^(b.bits.length+1) = 0 := Nat.div_eq_of_lt (by
      rw [Nat.size_eq_bits_len]; exact (Nat.lt_size_self b).trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_succ _)))
    simp [radiusTest,hdiv] at ht
    omega
  have haux (n : ℕ) (hn : n ≤ b.bits.length+1) : ((List.range n).filter (scanTest b deg)).length = min (n-1) r := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ,List.filter_append,List.length_append,ih (by omega)]
      have hm : min n b.bits.length = n := min_eq_left (by omega)
      by_cases h1 : n=0
      · subst n; simp [scanTest]
      by_cases h2 : n=1
      · subst n; simp [scanTest]; omega
      have htest := radiusTest_correct b deg n hb (by omega)
      by_cases h3 : n ≤ r
      · have ht := htest.mpr h3
        have hs : scanTest b deg n = true := by simpa [scanTest,radiusTest,hm,h2,show 2 ≤ n by omega] using ht
        simp [hs]; omega
      · have ht : radiusTest b deg n = false := Bool.eq_false_iff.mpr (fun h => h3 (htest.mp h))
        have hs : scanTest b deg n = false := by simpa [scanTest,radiusTest,hm,h2,show 2 ≤ n by omega] using ht
        simp [hs]; omega
  simpa [radiusScan,min_eq_right hl] using haux (b.bits.length+1) (le_refl _)

end DetDLP.D1

open DetDLP.D1
theorem solution : (∀ b deg : ℕ, 2 ≤ b → radiusScan (b,deg) = radius b deg) ∧ Groundwork.PolyT radiusScan := ⟨radiusScan_eq,radiusScan_poly⟩
