-- Prove2me | solution 1 for Formalism.RankGapBounds.LocalQuadraticParts.pm_y_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:57:42.468622+00:00
-- url     : https://prove2.me/submissions/711f16c1-4df0-4f9c-95ec-4474939562c3

import Definitions.Def_Formalism_RankGapBounds_RandomSubsetCounterexample
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_PmModulusFacts
import Theorems.Thm_Formalism_RankGapBounds_LocalQuadraticParts_pm_sum_cover
import Theorems.Thm_Formalism_RankGapBounds_LocalQuadraticParts_pm_key_Y
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.RankGapBounds.LocalQuadraticParts
open Finset
private theorem log_le_log_of_pos_of_le {a b : ℝ} (ha : 0 < a) (h : a ≤ b) : Real.log a ≤ Real.log b := by
  exact Real.log_le_log ha h
private theorem log_natCast_nonneg_real (n : ℕ) : 0 ≤ Real.log n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [h]
  · exact Real.log_nonneg (Nat.one_le_cast.mpr h)
private theorem sum_range_inv_succ_le_one_add_log (N : ℕ) :
    ∑ k ∈ range N, 1 / ((k : ℝ) + 1) ≤ 1 + Real.log N := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    rcases Nat.eq_zero_or_pos n with h0 | hn
    · subst h0; simp
    · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have hstep : 1 / ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1) - Real.log n := by
        have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < n / (n + 1) by positivity)
        rw [Real.log_div hn'.ne' (by positivity)] at h
        have h' : (n : ℝ) / (n + 1) - 1 = -(1 / ((n : ℝ) + 1)) := by
          field_simp
          ring
        linarith
      push_cast
      linarith
end Formalism.RankGapBounds.LocalQuadraticParts
end

set_option autoImplicit false
open Formalism Formalism.RankGapBounds Formalism.RankGapBounds.LocalQuadraticParts
open Finset
namespace Formalism.RankGapBounds.LocalQuadraticParts
theorem _root_.solution (M N : ℕ) (hM : 2 ≤ M) (Y : ℝ) (hY : 1 ≤ Y) (hNY : (N : ℝ) ≤ Y) (s : Finset ℕ)
    (hs : ∀ l ∈ s, 3 ≤ l ∧ l ≤ N ∧ ((l : ZMod M) = 1 ∨ (l : ZMod M) = -1))
    (hsY : ∀ l ∈ s, (l : ℝ) ≤ Y) :
    ∑ l ∈ s, Real.log l / (l : ℝ) ≤ 4 * Real.log Y * (1 + Real.log Y) / M := by
  have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hlY : 0 ≤ Real.log Y := Real.log_nonneg hY
  set f : ℕ → ℝ := fun l => if (l : ℝ) ≤ Y then Real.log l / (l : ℝ) else 0 with hfdef
  have hf0 : ∀ l, 0 ≤ f l := by
    intro l
    simp only [hfdef]
    split_ifs
    · exact div_nonneg (log_natCast_nonneg_real l) (Nat.cast_nonneg l)
    · exact le_rfl
  have hsf : ∑ l ∈ s, Real.log l / (l : ℝ) = ∑ l ∈ s, f l := by
    apply sum_congr rfl
    intro l hl
    simp only [hfdef]
    rw [if_pos (hsY l hl)]
  have hmain := pm_sum_cover f hf0 M N hM s hs
  have hterm : ∀ k m : ℕ, ((k : ℝ) + 1) * M / 2 ≤ m → 1 ≤ m →
      f m ≤ Real.log Y * (2 / M) * (1 / ((k : ℝ) + 1)) := by
    intro k m h1 hm1
    have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg k)
    have hnn : 0 ≤ Real.log Y * (2 / M) * (1 / ((k : ℝ) + 1)) :=
      mul_nonneg (mul_nonneg hlY (by positivity)) (by positivity)
    simp only [hfdef]
    split_ifs with hmY
    · exact pm_key_Y m ((k : ℝ) + 1) M Y hk1 (by linarith) h1 hmY
        (by exact_mod_cast hm1)
    · exact hnn
  have hsumk : ∑ k ∈ range N, Real.log Y * (2 / M) * (1 / ((k : ℝ) + 1)) ≤
      2 * Real.log Y * (1 + Real.log Y) / M := by
    rw [← mul_sum]
    have hH := sum_range_inv_succ_le_one_add_log N
    have hNl : 1 + Real.log N ≤ 1 + Real.log Y := by
      rcases Nat.eq_zero_or_pos N with h0 | h0
      · rw [h0, Nat.cast_zero, Real.log_zero]; linarith
      · have : (0 : ℝ) < N := by exact_mod_cast h0
        have := log_le_log_of_pos_of_le this hNY
        linarith
    calc Real.log Y * (2 / M) * ∑ k ∈ range N, 1 / ((k : ℝ) + 1)
        ≤ Real.log Y * (2 / M) * (1 + Real.log Y) :=
          mul_le_mul_of_nonneg_left (hH.trans hNl) (mul_nonneg hlY (by positivity))
      _ = 2 * Real.log Y * (1 + Real.log Y) / M := by ring
  have hA : ∑ k ∈ range N, f ((k + 1) * M + 1) ≤
      ∑ k ∈ range N, Real.log Y * (2 / M) * (1 / ((k : ℝ) + 1)) := by
    apply sum_le_sum
    intro k _
    apply hterm k
    · have hkM : (0 : ℝ) ≤ (k : ℝ) * M := mul_nonneg (Nat.cast_nonneg k) hM0.le
      push_cast
      nlinarith
    · omega
  have hB : ∑ k ∈ range N, f ((k + 1) * M - 1) ≤
      ∑ k ∈ range N, Real.log Y * (2 / M) * (1 / ((k : ℝ) + 1)) := by
    apply sum_le_sum
    intro k _
    have h1le : 1 * M ≤ (k + 1) * M := Nat.mul_le_mul (by omega) (le_refl M)
    apply hterm k
    · have hkM : (0 : ℝ) ≤ (k : ℝ) * M := mul_nonneg (Nat.cast_nonneg k) hM0.le
      rw [Nat.cast_sub (by omega)]
      push_cast
      nlinarith
    · omega
  calc ∑ l ∈ s, Real.log l / (l : ℝ) = ∑ l ∈ s, f l := hsf
    _ ≤ _ := hmain
    _ ≤ 2 * Real.log Y * (1 + Real.log Y) / M + 2 * Real.log Y * (1 + Real.log Y) / M :=
        add_le_add (hA.trans hsumk) (hB.trans hsumk)
    _ = 4 * Real.log Y * (1 + Real.log Y) / M := by ring
end Formalism.RankGapBounds.LocalQuadraticParts
