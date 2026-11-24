-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.pair_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:53:04.291845+00:00
-- url     : https://prove2.me/submissions/a4e986a6-7988-4f69-9583-8d6881b740e4

import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeVariationUnbounded
import Mathlib
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_LogVandermondeVariationUnbounded
import Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_abs_log_sub_le_of
import Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_abs_log_sub_le_log
import Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_gap_sum
import Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_dist_cast

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.StandardLattice
open Finset
namespace Formalism.LogVandermondeBounds.StandardLattice
theorem _root_.solution {n : ℕ} {Δ : ℝ} {u u' : Fin (n + 2) → ℝ} (hw : WordPair n Δ u u')
    (a b : Fin (n + 2)) (hab : a < b) :
    |Real.log (u a - u b) - Real.log (u' a - u' b)| ≤
      2 / (((b.val - a.val - 1 : ℕ) : ℝ) + 1) +
      ((if a = 0 ∧ b = ⟨1, by omega⟩ then Real.log (1 + Δ) else 0) +
       (if a = ⟨n, by omega⟩ ∧ b = Fin.last (n + 1) then Real.log (1 + Δ) else 0)) := by
  obtain ⟨hΔ, h1, h1', hcl, h0, hl, hg⟩ := hw
  have hL : 0 ≤ Real.log (1 + Δ) := Real.log_nonneg (by linarith)
  have hab' : a.val < b.val := hab
  have hbn : b.val < n + 2 := b.isLt
  rw [dist_cast a b hab]
  have hD := h1 a b hab
  have hD' := h1' a b hab
  have hca := abs_le.mp (hcl a)
  have hcb := abs_le.mp (hcl b)
  have hI0 : 0 ≤ (if a = 0 ∧ b = ⟨1, by omega⟩ then Real.log (1 + Δ) else 0) := by
    split_ifs <;> linarith
  have hI1 : 0 ≤ (if a = ⟨n, by omega⟩ ∧ b = Fin.last (n + 1) then Real.log (1 + Δ) else 0) := by
    split_ifs <;> linarith
  have hablt : (a.val : ℝ) < b.val := by exact_mod_cast hab'
  have hd : 0 < (b.val : ℝ) - a.val := by linarith
  have h2d : 0 ≤ 2 / ((b.val : ℝ) - a.val) := by positivity
  have gu := gap_sum u (3 * Δ) (fun i j hi hj hjn => (hg i j hi hj hjn).1)
  have gu' := gap_sum u' (3 * Δ) (fun i j hi hj hjn => (hg i j hi hj hjn).2)
  rcases (by omega : (a.val = 0 ∧ b.val = n + 1) ∨ (a.val = 0 ∧ b.val = 1) ∨
      (a.val = n ∧ b.val = n + 1) ∨ (a.val = 0 ∧ 2 ≤ b.val ∧ b.val ≤ n) ∨
      (1 ≤ a.val ∧ a.val + 1 ≤ n ∧ b.val = n + 1) ∨ (1 ≤ a.val ∧ b.val ≤ n))
    with hc | hc | hc | hc | hc | hc
  · have ea : a = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
    have eb : b = Fin.last (n + 1) := Fin.ext (by rw [Fin.val_last]; omega)
    rw [← ea] at h0
    rw [← eb] at hl
    have key : |Real.log (u a - u b) - Real.log (u' a - u' b)| = 0 := by
      rw [h0, hl, sub_self, abs_zero]
    linarith
  · have ea : a = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
    have eb : b = ⟨1, by omega⟩ := Fin.ext (by show b.val = 1; omega)
    have hI : (if a = 0 ∧ b = ⟨1, by omega⟩ then Real.log (1 + Δ) else 0) = Real.log (1 + Δ) :=
      if_pos ⟨ea, eb⟩
    rw [← ea] at h0
    have hb : |(u a - u b) - (u' a - u' b)| ≤ Δ := by
      rw [abs_le]; constructor <;> linarith
    have := abs_log_sub_le_log hD hD' hb
    linarith
  · have ea : a = ⟨n, by omega⟩ := Fin.ext (by show a.val = n; omega)
    have eb : b = Fin.last (n + 1) := Fin.ext (by rw [Fin.val_last]; omega)
    have hI : (if a = ⟨n, by omega⟩ ∧ b = Fin.last (n + 1) then Real.log (1 + Δ) else 0) =
        Real.log (1 + Δ) := if_pos ⟨ea, eb⟩
    rw [← eb] at hl
    have hb : |(u a - u b) - (u' a - u' b)| ≤ Δ := by
      rw [abs_le]; constructor <;> linarith
    have := abs_log_sub_le_log hD hD' hb
    linarith
  · have ea : a = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
    let b1 : Fin (n + 2) := ⟨1, by omega⟩
    have hb1 : (0 : Fin (n + 2)) < b1 := by rw [Fin.lt_def, Fin.val_zero]; simp [b1]
    have g1 := gu b1 (by simp [b1]) (b.val - 1) b (by simp [b1]; omega) hc.2.2
    have g1' := gu' b1 (by simp [b1]) (b.val - 1) b (by simp [b1]; omega) hc.2.2
    have e01 := h1 0 b1 hb1
    have e01' := h1' 0 b1 hb1
    rw [← ea] at e01 e01' h0
    have hcast : ((b.val - 1 : ℕ) : ℝ) = (b.val : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [hcast] at g1 g1'
    have hav : (a.val : ℝ) = 0 := by exact_mod_cast hc.1
    have hb2 : (2 : ℝ) ≤ b.val := by exact_mod_cast hc.2.1
    have hm : 0 < 3 * Δ * ((b.val : ℝ) - 1) := by
      have : (0 : ℝ) < (b.val : ℝ) - 1 := by linarith
      positivity
    have hb : |(u a - u b) - (u' a - u' b)| ≤ Δ := by
      rw [abs_le]; constructor <;> linarith
    have key := abs_log_sub_le_of hm (by linarith) (by linarith) hb
    have hfin : Δ / (3 * Δ * ((b.val : ℝ) - 1)) ≤ 2 / ((b.val : ℝ) - a.val) := by
      rw [hav, sub_zero, div_le_div_iff₀ hm (by linarith)]
      nlinarith
    linarith
  · let an : Fin (n + 2) := ⟨n, by omega⟩
    have eb : b = Fin.last (n + 1) := Fin.ext (by rw [Fin.val_last]; omega)
    have han : an < Fin.last (n + 1) := by rw [Fin.lt_def, Fin.val_last]; simp [an]
    have g1 := gu a hc.1 (n - a.val) an (by simp [an]; omega) (by simp [an])
    have g1' := gu' a hc.1 (n - a.val) an (by simp [an]; omega) (by simp [an])
    have e01 := h1 an _ han
    have e01' := h1' an _ han
    rw [← eb] at e01 e01' hl
    have hcast : ((n - a.val : ℕ) : ℝ) = (n : ℝ) - a.val := by
      rw [Nat.cast_sub (by omega)]
    rw [hcast] at g1 g1'
    have hbv : (b.val : ℝ) = n + 1 := by exact_mod_cast hc.2.2
    have ha2 : (a.val : ℝ) + 1 ≤ n := by exact_mod_cast hc.2.1
    have hm : 0 < 3 * Δ * ((n : ℝ) - a.val) := by
      have : (0 : ℝ) < (n : ℝ) - a.val := by linarith
      positivity
    have hb : |(u a - u b) - (u' a - u' b)| ≤ Δ := by
      rw [abs_le]; constructor <;> linarith
    have key := abs_log_sub_le_of hm (by linarith) (by linarith) hb
    have hfin : Δ / (3 * Δ * ((n : ℝ) - a.val)) ≤ 2 / ((b.val : ℝ) - a.val) := by
      rw [hbv, div_le_div_iff₀ hm (by linarith)]
      nlinarith
    linarith
  · have g1 := gu a hc.1 (b.val - a.val) b (by omega) hc.2
    have g1' := gu' a hc.1 (b.val - a.val) b (by omega) hc.2
    have hcast : ((b.val - a.val : ℕ) : ℝ) = (b.val : ℝ) - a.val := by
      rw [Nat.cast_sub (by omega)]
    rw [hcast] at g1 g1'
    have hm : 0 < 3 * Δ * ((b.val : ℝ) - a.val) := by positivity
    have hb : |(u a - u b) - (u' a - u' b)| ≤ 2 * Δ := by
      rw [abs_le]; constructor <;> linarith
    have key := abs_log_sub_le_of hm (by linarith) (by linarith) hb
    have hfin : 2 * Δ / (3 * Δ * ((b.val : ℝ) - a.val)) ≤ 2 / ((b.val : ℝ) - a.val) := by
      rw [div_le_div_iff₀ hm hd]
      nlinarith
    linarith
end Formalism.LogVandermondeBounds.StandardLattice
