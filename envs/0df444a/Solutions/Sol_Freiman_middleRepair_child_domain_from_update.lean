-- Prove2me | solution 1 for Freiman.middleRepair_child_domain_from_update
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T22:51:25.648221+00:00
-- url     : https://prove2.me/submissions/b5769d78-8bf3-410f-9525-ca843b97728c

import Definitions.Def_Freiman_middleRepair
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs

open Freiman

private theorem prefix_injective (w : List ℕ+) : Function.Injective (prefixEval w) := by
  induction w with
  | nil => exact Function.injective_id
  | cons a w ih =>
    intro x y h
    apply ih
    apply add_left_cancel (a := ((a : ℕ) : ℝ))
    exact inv_injective (by simpa only [prefixEval, one_div] using h)

private theorem width_positive (w : List ℕ+) : 0 < middleWidth w := by
  apply abs_pos.mpr
  apply sub_ne_zero.mpr
  intro h
  have heq := prefix_injective w h
  have hs : 3 < Real.sqrt 21 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  unfold middleBeta middleAlpha at heq
  linarith

private theorem normalization_regular (c : MiddleCore) (hc : middleRegular c) :
    middleRegular (middleNormalized c) := by
  unfold middleNormalized
  split_ifs
  · exact hc
  · exact ⟨hc.2.1, hc.1, hc.2.2.2, hc.2.2.1⟩

theorem solution :
    (∀ (w : List ℕ+) (a : ℕ+), middleParameter (w ++ [a]) = 1 / (((a:ℕ):ℝ)+middleParameter w)) →
    (∀ (p : ℝ) (a : ℕ+), p ∈ Set.Icc (1/4:ℝ) (4/5) → (a:ℕ) ≤ 3 → 1/(((a:ℕ):ℝ)+p) ∈ Set.Icc (1/4:ℝ) (4/5)) →
    ∀ (c : MiddleCore) (u v : List ℕ+), middleRegular c → middleDigits123 u → middleDigits123 v →
      0 < u.length+v.length → middleRegular (middleRepairChild c u v) ∧ middleRepairProper c (middleRepairChild c u v) := by
  intro update rectangle c u v hc hu hv hpos
  have extension (w z : List ℕ+) (hw : middleParameter w ∈ Set.Icc (1/4:ℝ) (4/5))
      (hz : middleDigits123 z) : middleParameter (w ++ z) ∈ Set.Icc (1/4:ℝ) (4/5) := by
    induction z using List.reverseRecOn with
    | nil => simpa using hw
    | append_singleton z a ih =>
      have hza : (a : ℕ) ≤ 3 := hz a (by simp)
      have hz' : middleDigits123 z := fun b hb => hz b (by simp [hb])
      rw [← List.append_assoc, update]
      exact rectangle _ a (ih hz') hza
  have hn := normalization_regular c hc
  constructor
  · apply normalization_regular
    exact ⟨extension _ u hn.1 hu, extension _ v hn.2.1 hv,
      width_positive _, width_positive _⟩
  · exact ⟨u, v, hu, hv, hpos, rfl⟩

#print axioms solution
