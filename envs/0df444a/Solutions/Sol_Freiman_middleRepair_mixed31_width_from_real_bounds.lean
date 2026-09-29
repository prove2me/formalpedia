-- Prove2me | solution 1 for Freiman.middleRepair_mixed31_width_from_real_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-10T09:40:24.004272+00:00
-- url     : https://prove2.me/submissions/fe7eabe5-1152-420e-9c7e-1ee38910225c

import Definitions.Def_Freiman_middleRepair
import Theorems.Thm_Freiman_middle_width_identity
import Theorems.Thm_Freiman_middle_continuant_growth
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

open Freiman

namespace FreimanM8Mixed3120260910

private theorem cd_append (w : List ℕ+) (a : ℕ+) :
    middleCD (w ++ [a]) = ((middleCD w).2, (middleCD w).1 + ((a:ℕ):ℝ)*(middleCD w).2) := by
  simp [middleCD, List.foldl_append]

private theorem alpha_beta_positive : 0 < middleAlpha ∧ 0 < middleBeta ∧ middleAlpha < middleBeta := by
  have hs : 3 < Real.sqrt 21 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  unfold middleAlpha middleBeta
  constructor
  · linarith
  constructor <;> linarith

private theorem width_singleton (w : List ℕ+) (a : ℕ+) :
    middleWidth (w ++ [a]) = (middleBeta-middleAlpha) /
      ((middleCD w).2^2 * (((a:ℕ):ℝ)+middleParameter w+middleAlpha) *
        (((a:ℕ):ℝ)+middleParameter w+middleBeta)) := by
  have hg := middle_continuant_growth w
  have hDpos := hg.2.1
  have hD : (middleCD w).2 ≠ 0 := ne_of_gt hg.2.1
  have hC : 0 ≤ (middleCD w).1 := by
    have h := mul_nonneg hg.1 (le_of_lt hDpos)
    simpa only [middleParameter, div_mul_cancel₀ _ hD] using h
  have ha : (0:ℝ) < (a:ℕ) := by exact_mod_cast a.pos
  have hsum : 0 < (middleCD w).1 + ((a:ℕ):ℝ)*(middleCD w).2 := by positivity
  have hab := alpha_beta_positive
  have hA : 0 < ((a:ℕ):ℝ)+middleParameter w+middleAlpha := by linarith [hg.1,hab.1]
  have hB : 0 < ((a:ℕ):ℝ)+middleParameter w+middleBeta := by linarith [hg.1,hab.2.1]
  rw [middle_width_identity]
  unfold middleParameter
  rw [cd_append]
  simp only
  field_simp (disch := positivity)
  <;> ring

private theorem normalize_idem (c : MiddleCore) :
    middleNormalized (middleNormalized c) = middleNormalized c := by
  unfold middleNormalized
  split_ifs with h h'
  all_goals try rfl
  all_goals simp_all only [not_le]
  all_goals linarith

private theorem normalize_regular (c : MiddleCore) (hc : middleRegular c) :
    middleRegular (middleNormalized c) := by
  unfold middleNormalized
  split_ifs
  · exact hc
  · exact ⟨hc.2.1, hc.1, hc.2.2.2, hc.2.2.1⟩


private theorem width_pos (w : List ℕ+) : 0 < middleWidth w := by
  have hg := middle_continuant_growth w
  have hab := alpha_beta_positive
  have hD := hg.2.1
  have hp := hg.1
  have hA := hab.1
  have hB := hab.2.1
  rw [middle_width_identity]
  apply div_pos (sub_pos.mpr hab.2.2)
  positivity

private theorem ratio_singletons (u v : List ℕ+) :
    middleWidth (u ++ [3]) / middleWidth (v ++ [1]) =
      middleMixedK (middleParameter u) (middleParameter v) /
        ((middleCD u).2^2 / (middleCD v).2^2) := by
  have hu := middle_continuant_growth u
  have hv := middle_continuant_growth v
  have hab := alpha_beta_positive
  have hdelta : middleBeta-middleAlpha ≠ 0 := ne_of_gt (sub_pos.mpr hab.2.2)
  have ha3 : 0 < 3+middleParameter u+middleAlpha := by linarith [hu.1,hab.1]
  have hb3 : 0 < 3+middleParameter u+middleBeta := by linarith [hu.1,hab.2.1]
  have ha1 : 0 < 1+middleParameter v+middleAlpha := by linarith [hv.1,hab.1]
  have hb1 : 0 < 1+middleParameter v+middleBeta := by linarith [hv.1,hab.2.1]
  rw [width_singleton, width_singleton]
  norm_num only [PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one]
  unfold middleMixedK
  field_simp [hdelta, ne_of_gt hu.2.1, ne_of_gt hv.2.1, ne_of_gt ha3,
    ne_of_gt hb3, ne_of_gt ha1, ne_of_gt hb1]
  <;> ring

end FreimanM8Mixed3120260910

open FreimanM8Mixed3120260910

theorem solution :
    (∀ p s : ℝ, p ∈ Set.Icc (1/4:ℝ) (4/5) → s ∈ Set.Icc (1/4:ℝ) (4/5) → middleScalarA p s (55/100)<(19/5:ℝ)*middleMixedK p s ∧ (5/19:ℝ)*middleMixedK p s<middleScalarB p s (328/1000)) →
    ∀ c : MiddleCore, middleRegular c → middleRowCondition c .mixedC →
      middleRatio (middleRepairChild c [3] [1]) < (19/5:ℝ) := by
  intro hnum c hc hrow
  let d := middleNormalized c
  have hd : middleRegular d := normalize_regular c hc
  let q := (middleCD d.left).2^2 / (middleCD d.right).2^2
  let K := middleMixedK (middleParameter d.left) (middleParameter d.right)
  have hbounds := hnum (middleParameter d.left) (middleParameter d.right) hd.1 hd.2.1
  have hqa : q ≤ middleScalarA (middleParameter d.left) (middleParameter d.right) (55/100) := by
    exact hrow.2.1
  have hbq : middleScalarB (middleParameter d.left) (middleParameter d.right) (328/1000) ≤ q := by
    exact hrow.2.2
  have hqlo : (5/19:ℝ)*K < q := lt_of_lt_of_le hbounds.2 hbq
  have hqhi : q < (19/5:ℝ)*K := lt_of_le_of_lt hqa hbounds.1
  have hl := (middle_continuant_growth d.left).2.1
  have hr := (middle_continuant_growth d.right).2.1
  have hqpos : 0 < q := div_pos (sq_pos_of_pos hl) (sq_pos_of_pos hr)
  let X := middleWidth (d.left ++ [3])
  let Y := middleWidth (d.right ++ [1])
  have hX : 0 < X := width_pos _
  have hY : 0 < Y := width_pos _
  have hxy : X/Y = K/q := ratio_singletons d.left d.right
  have hxylt : X/Y < (19/5:ℝ) := by
    rw [hxy]
    apply (div_lt_iff₀ hqpos).2
    nlinarith only [hqlo]
  have heq : X*q = K*Y := (div_eq_div_iff (ne_of_gt hY) (ne_of_gt hqpos)).mp hxy
  have hyxlt : Y/X < (19/5:ℝ) := by
    apply (div_lt_iff₀ hX).2
    have hmul : Y*q < ((19/5:ℝ)*X)*q := by
      nlinarith only [mul_lt_mul_of_pos_right hqhi hY, heq]
    by_contra hn
    have hge := mul_le_mul_of_nonneg_right (le_of_not_gt hn) (le_of_lt hqpos)
    linarith
  unfold middleRatio middleRepairChild
  rw [FreimanM8Mixed3120260910.normalize_idem]
  change middleWidth (middleNormalized ⟨d.left ++ [3],d.right ++ [1]⟩).left /
    middleWidth (middleNormalized ⟨d.left ++ [3],d.right ++ [1]⟩).right < (19/5:ℝ)
  unfold middleNormalized
  split_ifs
  · exact hxylt
  · exact hyxlt

#print axioms solution
