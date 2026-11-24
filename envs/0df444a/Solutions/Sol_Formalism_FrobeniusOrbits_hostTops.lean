-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.hostTops
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:09:58.097802+00:00
-- url     : https://prove2.me/submissions/e7414a16-2d01-487b-8408-6b062e946a3f

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickFrames
import Theorems.Thm_Formalism_FrobeniusOrbits_BernoulliSumsFrobeniusOrbits_bern_nonneg
import Theorems.Thm_Formalism_FrobeniusOrbits_BernoulliSumsFrobeniusOrbits_sum_bern
import Theorems.Thm_Formalism_FrobeniusOrbits_BernoulliSumsFrobeniusOrbits_sum_bern_var

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open BernoulliSumsFrobeniusOrbits
open Classical
namespace Formalism.FrobeniusOrbits
theorem _root_.solution : HostTops := by
  intro α ι _ _ δ β ω BAD hδ hδ1 hβ hω hn hBAD
  set n : ℝ := (Fintype.card α : ℝ) with hn_def
  set M : ℝ := β * δ * n * ∑ p, ω p with hM_def
  set X : Finset α → ℝ := fun T => ∑ p, ω p * ((T.filter (fun t => BAD p t T)).card : ℝ)
    with hX_def
  have hb0 : ∀ T : Finset α, 0 ≤ bern δ T := bern_nonneg hδ.le hδ1
  have hX0 : ∀ T, 0 ≤ X T := fun T => sum_nonneg fun p _ => mul_nonneg (hω p) (Nat.cast_nonneg _)
  have hM0 : 0 ≤ M := by
    have : 0 ≤ ∑ p, ω p := sum_nonneg fun p _ => hω p
    have : 0 ≤ n := Nat.cast_nonneg _
    positivity

  have hc : ∀ p (T : Finset α), ((T.filter (fun t => BAD p t T)).card : ℝ) =
      ∑ t, if t ∈ T ∧ BAD p t T then (1 : ℝ) else 0 := by
    intro p T
    rw [Finset.sum_boole]
    congr 2
    ext t
    simp
  have hEX : ∑ T, bern δ T * X T ≤ M := by
    calc ∑ T, bern δ T * X T
        = ∑ T : Finset α, ∑ p, ∑ t, ω p * (if t ∈ T ∧ BAD p t T then bern δ T else 0) := by
          refine sum_congr rfl fun T _ => ?_
          simp only [X, hc, mul_sum]
          refine sum_congr rfl fun p _ => sum_congr rfl fun t _ => ?_
          split_ifs <;> ring
      _ = ∑ p, ∑ t, ω p * ∑ T : Finset α, (if t ∈ T ∧ BAD p t T then bern δ T else 0) := by
          rw [sum_comm]
          refine sum_congr rfl fun p _ => ?_
          rw [sum_comm]
          simp only [mul_sum]
      _ ≤ ∑ p, ∑ _t : α, ω p * (β * δ) :=
          sum_le_sum fun p _ => sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hBAD p t) (hω p)
      _ = M := by
          simp only [hM_def, hn_def, sum_const, card_univ, nsmul_eq_mul, mul_sum]
          refine sum_congr rfl fun p _ => ?_
          ring

  have hA : ∑ T : Finset α, (if 4 * M < X T then bern δ T else 0) ≤ 1 / 4 := by
    have key : 4 * M * ∑ T : Finset α, (if 4 * M < X T then bern δ T else 0) ≤ M := by
      rw [mul_sum]
      refine le_trans (sum_le_sum fun T _ => ?_) hEX
      split_ifs with h
      · nlinarith [hb0 T]
      · simp only [mul_zero]; exact mul_nonneg (hb0 T) (hX0 T)
    rcases hM0.lt_or_eq with hpos | hzero
    · nlinarith
    · have hsum0 : ∑ T, bern δ T * X T = 0 :=
        le_antisymm (hzero ▸ hEX) (sum_nonneg fun T _ => mul_nonneg (hb0 T) (hX0 T))
      have hall := (Finset.sum_eq_zero_iff_of_nonneg
        (fun T _ => mul_nonneg (hb0 T) (hX0 T))).mp hsum0
      have : ∑ T : Finset α, (if 4 * M < X T then bern δ T else 0) = 0 := by
        refine sum_eq_zero fun T _ => ?_
        split_ifs with h
        · have hXT : 0 < X T := by rw [← hzero] at h; linarith
          have := hall T (mem_univ _)
          rcases mul_eq_zero.mp this with h' | h'
          · exact h'
          · linarith
        · rfl
      rw [this]; norm_num

  have hB : ∑ T : Finset α,
      (if (δ * n / 2) ^ 2 < ((T.card : ℝ) - δ * n) ^ 2 then bern δ T else 0) ≤ 1 / 4 := by
    set S := ∑ T : Finset α,
      (if (δ * n / 2) ^ 2 < ((T.card : ℝ) - δ * n) ^ 2 then bern δ T else 0) with hS
    have hS0 : 0 ≤ S := sum_nonneg fun T _ => by split_ifs <;> simp [hb0 T]
    have key : (δ * n / 2) ^ 2 * S ≤ δ * n := by
      have hv := sum_bern_var (α := α) δ
      rw [hS, mul_sum]
      calc ∑ T : Finset α, (δ * n / 2) ^ 2 *
            (if (δ * n / 2) ^ 2 < ((T.card : ℝ) - δ * n) ^ 2 then bern δ T else 0)
          ≤ ∑ T : Finset α, bern δ T * ((T.card : ℝ) - δ * n) ^ 2 := by
            refine sum_le_sum fun T _ => ?_
            split_ifs with h
            · nlinarith [hb0 T]
            · simp only [mul_zero]; exact mul_nonneg (hb0 T) (sq_nonneg _)
        _ = n * δ * (1 - δ) := hv
        _ ≤ δ * n := by nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card α)]
    by_contra hlt
    push Not at hlt
    have hc0 : 0 < δ * n := by linarith
    have h1 : (δ * n / 2) ^ 2 * (1 / 4) < (δ * n / 2) ^ 2 * S :=
      mul_lt_mul_of_pos_left hlt (by positivity)
    nlinarith [hn]

  by_contra hne
  push Not at hne
  have hle : ∀ T : Finset α, bern δ T ≤ (if 4 * M < X T then bern δ T else 0) +
      (if (δ * n / 2) ^ 2 < ((T.card : ℝ) - δ * n) ^ 2 then bern δ T else 0) := by
    intro T
    by_cases h2 : (δ * n / 2) ^ 2 < ((T.card : ℝ) - δ * n) ^ 2
    · rw [if_pos h2]; split_ifs <;> linarith [hb0 T]
    · rw [if_neg h2]
      have hab := abs_le_of_sq_le_sq' (not_lt.mp h2) (by positivity)
      have h4 : 4 * M < X T := by
        have := hne T (by linarith [hab.1]) (by linarith [hab.2])
        simp only [X, hM_def]
        linarith
      rw [if_pos h4]; linarith
  have := sum_le_sum fun T (_ : T ∈ (univ : Finset (Finset α))) => hle T
  rw [sum_add_distrib, sum_bern] at this
  linarith
end Formalism.FrobeniusOrbits
