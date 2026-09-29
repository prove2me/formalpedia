-- Prove2me | solution 1 for Freiman.middleRepair_j_ratio_specialization
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-10T10:07:24.465496+00:00
-- url     : https://prove2.me/submissions/7a5b5439-756a-403c-8bad-e958e0e47f4e

import Definitions.Def_Freiman_middleRepair
import Theorems.Thm_Freiman_middle_width_identity
import Theorems.Thm_Freiman_middle_continuant_growth
import Theorems.Thm_Freiman_prefixEval_difference
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.SplitIfs

open Freiman

namespace FreimanM8JRatio20260910

private theorem cd_append (w : List ℕ+) (a : ℕ+) :
    middleCD (w++[a]) = ((middleCD w).2,(middleCD w).1+((a:ℕ):ℝ)*(middleCD w).2) := by
  simp [middleCD, List.foldl_append]

private theorem local_continuant_append (w : List ℕ+) (a : ℕ+) :
    wordContinuantData (w ++ [a]) =
      ((wordContinuantP w, (a:ℕ)*wordContinuantP w+wordContinuantPrevP w),
       (wordContinuantQ w, (a:ℕ)*wordContinuantQ w+wordContinuantPrevQ w)) := by
  simp [wordContinuantData, wordContinuantP, wordContinuantPrevP, wordContinuantQ,
    wordContinuantPrevQ, List.foldl_append]

private theorem cd_coordinates (w : List ℕ+) :
    middleCD w = ((wordContinuantPrevQ w : ℝ),(wordContinuantQ w : ℝ)) := by
  induction w using List.reverseRecOn with
  | nil => norm_num [middleCD, wordContinuantPrevQ, wordContinuantQ, wordContinuantData]
  | append_singleton w a ih =>
    rw [cd_append, ih]
    simp only [wordContinuantQ, wordContinuantPrevQ, local_continuant_append]
    push_cast
    congr 1
    ring

private theorem pe_unit (w : List ℕ+) (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) :
    prefixEval w x ∈ Set.Icc (0:ℝ) 1 := by
  induction w with
  | nil => exact hx
  | cons a w ih =>
    have ha : (1:ℝ) ≤ ((a:ℕ):ℝ) := by exact_mod_cast a.one_le
    change 0 ≤ 1/(((a:ℕ):ℝ)+prefixEval w x) ∧ 1/(((a:ℕ):ℝ)+prefixEval w x) ≤ 1
    have hpos : 0 < ((a:ℕ):ℝ)+prefixEval w x := by linarith [ih.1]
    constructor
    · exact le_of_lt (div_pos (by norm_num) hpos)
    · apply (div_le_iff₀ hpos).2
      linarith [ih.1]

private theorem ab_unit : middleAlpha ∈ Set.Icc (0:ℝ) 1 ∧
    middleBeta ∈ Set.Icc (0:ℝ) 1 ∧ middleAlpha < middleBeta := by
  have h4 : (4:ℝ) ≤ Real.sqrt 21 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have h5 : Real.sqrt 21 ≤ (5:ℝ) := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  dsimp [middleAlpha, middleBeta]
  constructor
  · constructor <;> linarith
  constructor
  · constructor <;> linarith
  · linarith

private theorem pe_append (u v : List ℕ+) (x : ℝ) :
    prefixEval (u++v) x = prefixEval u (prefixEval v x) := by
  induction u with
  | nil => rfl
  | cons a u ih => simp only [List.cons_append, prefixEval, ih]

private theorem width_pos (w : List ℕ+) : 0 < middleWidth w := by
  have hg := middle_continuant_growth w
  have hp := hg.1
  have hD := hg.2.1
  have hA := ab_unit.1.1
  have hB := ab_unit.2.1.1
  rw [middle_width_identity]
  exact div_pos (sub_pos.mpr ab_unit.2.2) (by positivity)

private theorem width_append (w v : List ℕ+) : middleWidth (w++v) =
    middleWidth v / ((middleCD w).2^2 *
      (1+middleParameter w*prefixEval v middleAlpha) *
      (1+middleParameter w*prefixEval v middleBeta)) := by
  have ha := pe_unit v middleAlpha ab_unit.1
  have hb := pe_unit v middleBeta ab_unit.2.1
  have hD := (middle_continuant_growth w).2.1
  have hc := congrArg Prod.fst (cd_coordinates w)
  have hd := congrArg Prod.snd (cd_coordinates w)
  dsimp only at hc hd
  calc
    middleWidth (w++v) = middleWidth v /
        (((wordContinuantQ w:ℝ) + prefixEval v middleBeta*wordContinuantPrevQ w) *
         ((wordContinuantQ w:ℝ) + prefixEval v middleAlpha*wordContinuantPrevQ w)) := by
      simpa only [middleWidth, pe_append] using prefixEval_difference w _ _ hb ha
    _ = _ := by
      rw [← hc, ← hd]
      congr 1
      unfold middleParameter
      field_simp [ne_of_gt hD]

private theorem ratio_append (u w v : List ℕ+) :
    middleWidth (u++v) / middleWidth (w++v) =
      middleH (middleParameter u) (middleParameter w) (prefixEval v middleAlpha) (prefixEval v middleBeta) /
      ((middleCD u).2^2 / (middleCD w).2^2) := by
  have hu := middle_continuant_growth u
  have hw := middle_continuant_growth w
  have hup := hu.1
  have hwp := hw.1
  have ha := (pe_unit v middleAlpha ab_unit.1).1
  have hb := (pe_unit v middleBeta ab_unit.2.1).1
  have hdv := width_pos v
  rw [width_append, width_append]
  unfold middleH
  field_simp (disch := positivity)
  <;> ring



private theorem f3beta : prefixEval [3] middleBeta = middleAlpha := by
  have hsq : Real.sqrt (21:ℝ)^2 = 21 := Real.sq_sqrt (by norm_num)
  have hd : 0 < 3+middleBeta := by linarith [ab_unit.2.1.1]
  change 1/(3+middleBeta) = middleAlpha
  apply (div_eq_iff (ne_of_gt hd)).2
  unfold middleAlpha middleBeta
  nlinarith

private theorem f3alpha_le_beta : prefixEval [3] middleAlpha ≤ middleBeta := by
  have ha := ab_unit.1.1
  have h4 : (4:ℝ) ≤ Real.sqrt 21 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hb : (1/2:ℝ) ≤ middleBeta := by unfold middleBeta; linarith
  have h : prefixEval [3] middleAlpha ≤ (1/3:ℝ) := by
    change 1/(3+middleAlpha) ≤ (1/3:ℝ)
    apply (div_le_iff₀ (by linarith : 0 < 3+middleAlpha)).2
    linarith
  linarith

private theorem alpha_le_f3alpha : middleAlpha ≤ prefixEval [3] middleAlpha := by
  have ha := ab_unit.1.1
  calc
    middleAlpha = prefixEval [3] middleBeta := f3beta.symm
    _ ≤ _ := one_div_le_one_div_of_le (by linarith : 0 < 3+middleAlpha)
      (by linarith [ab_unit.2.2] : 3+middleAlpha ≤ 3+middleBeta)

private theorem f3_box (x : ℝ) (hx : x ∈ Set.Icc middleAlpha (prefixEval [3] middleAlpha)) :
    prefixEval [3] x ∈ Set.Icc middleAlpha (prefixEval [3] middleAlpha) := by
  have ha := ab_unit.1.1
  have hx0 : 0 ≤ x := ha.trans hx.1
  constructor
  · rw [← f3beta]
    exact one_div_le_one_div_of_le (by linarith : 0 < 3+x)
      (by linarith [hx.2, f3alpha_le_beta] : 3+x ≤ 3+middleBeta)
  · exact one_div_le_one_div_of_le (by linarith : 0 < 3+middleAlpha)
      (by linarith [hx.1] : 3+middleAlpha ≤ 3+x)

private theorem tails_box (k : ℕ) (hk : 1 ≤ k) :
    prefixEval (List.replicate k (3:ℕ+)) middleAlpha ∈ Set.Icc middleAlpha (prefixEval [3] middleAlpha) ∧
    prefixEval (List.replicate k (3:ℕ+)) middleBeta ∈ Set.Icc middleAlpha (prefixEval [3] middleAlpha) := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hz : k=0
    · subst k
      simp only [List.replicate_succ, List.replicate_zero]
      exact ⟨⟨alpha_le_f3alpha, le_rfl⟩, by rw [f3beta]; exact ⟨le_rfl,alpha_le_f3alpha⟩⟩
    · have h := ih (by omega)
      constructor
      · exact f3_box _ h.1
      · exact f3_box _ h.2

private theorem hStar_value (p s : ℝ) : middleHStar p s =
    (5/7:ℝ)*middleH p s (prefixEval [3] middleAlpha) (prefixEval [3] middleBeta) := by
  rw [f3beta]
  unfold middleHStar middleScalarThreshold middleH
  ring

private theorem q_pos (c : MiddleCore) : 0 < middleQ c := by
  have hl := (middle_continuant_growth (middleNormalized c).left).2.1
  have hr := (middle_continuant_growth (middleNormalized c).right).2.1
  exact div_pos (sq_pos_of_pos hl) (sq_pos_of_pos hr)

private theorem short1_iff (c : MiddleCore) : middleShort c 1 ↔
    middleHStar (middleParameter (middleNormalized c).left) (middleParameter (middleNormalized c).right) ≤ middleQ c := by
  rw [hStar_value]
  change middleWidth ((middleNormalized c).left++[3]) ≤
    (7/5:ℝ)*middleWidth ((middleNormalized c).right++[3]) ↔ _
  rw [← div_le_iff₀ (width_pos ((middleNormalized c).right++[3])), ratio_append]
  change _ /middleQ c ≤ (7/5:ℝ) ↔ _
  rw [div_le_iff₀ (q_pos c)]
  constructor <;> intro h <;> nlinarith only [h]

private theorem normalized_regular (c : MiddleCore) (hc : middleRegular c) :
    middleRegular (middleNormalized c) := by
  unfold middleNormalized
  split_ifs
  · exact hc
  · exact ⟨hc.2.1,hc.1,hc.2.2.2,hc.2.2.1⟩

end FreimanM8JRatio20260910

open FreimanM8JRatio20260910

theorem solution :
    (∀ p s x y : ℝ, p ∈ Set.Icc (1/4:ℝ) (4/5) → s ∈ Set.Icc (1/4:ℝ) (4/5) → x ∈ Set.Icc middleAlpha (prefixEval [3] middleAlpha) → y ∈ Set.Icc middleAlpha (prefixEval [3] middleAlpha) → middleHStar p s < middleH p s x y ∧ (5/19:ℝ)*middleH p s x y < middleScalarA p s (549/1000) ∧ (5/19:ℝ)*middleH p s x y < middleScalarB p s (313/1000)) →
    ∀ (c : MiddleCore) (r : MiddleRow) (k : ℕ), middleRegular c → middleRowCondition c r → middleEssentialJ r = true → 1 ≤ k →
      1 < middleWidth ((middleNormalized c).left ++ List.replicate k 3) / middleWidth ((middleNormalized c).right ++ List.replicate k 3) ∧ middleRatio (middleRepairJ c k)<(19/5:ℝ) := by
  intro hnum c r k hc hrow hj hk
  have hrows : ¬middleShort c 1 ∧
      (middleA c (549/1000) < middleQ c ∨ middleB c (313/1000) ≤ middleQ c) := by
    cases r <;> simp [middleEssentialJ] at hj
    · exact ⟨hrow.2.2, Or.inl hrow.2.1⟩
    · exact ⟨hrow.2.2.2.2, Or.inr hrow.2.2.1⟩
  let p := middleParameter (middleNormalized c).left
  let s := middleParameter (middleNormalized c).right
  let x := prefixEval (List.replicate k (3:ℕ+)) middleAlpha
  let y := prefixEval (List.replicate k (3:ℕ+)) middleBeta
  let H := middleH p s x y
  have hreg := normalized_regular c hc
  have hbox := tails_box k hk
  have hb := hnum p s x y hreg.1 hreg.2.1 hbox.1 hbox.2
  have hq0 := q_pos c
  have hqstar : middleQ c < middleHStar p s := lt_of_not_ge
    (fun h => hrows.1 ((short1_iff c).2 h))
  have hqH : middleQ c < H := lt_trans hqstar hb.1
  have hHq : (5/19:ℝ)*H < middleQ c := by
    rcases hrows.2 with ha | hb'
    · exact lt_trans hb.2.1 ha
    · exact lt_of_lt_of_le hb.2.2 hb'
  let X := middleWidth ((middleNormalized c).left ++ List.replicate k 3)
  let Y := middleWidth ((middleNormalized c).right ++ List.replicate k 3)
  have hY : 0 < Y := width_pos _
  have heq : X/Y = H/middleQ c := ratio_append _ _ _
  have hlt : 1 < X/Y := by
    rw [heq]
    apply (lt_div_iff₀ hq0).2
    simpa only [one_mul] using hqH
  have hbound : X/Y < (19/5:ℝ) := by
    rw [heq]
    apply (div_lt_iff₀ hq0).2
    nlinarith only [hHq]
  refine ⟨hlt, ?_⟩
  let d : MiddleCore := ⟨(middleNormalized c).left ++ List.replicate k 3,
    (middleNormalized c).right ++ List.replicate k 3⟩
  have hd : middleNormalized d = d := by
    apply if_pos
    change Y ≤ X
    have h := (lt_div_iff₀ hY).mp hlt
    linarith
  change middleRatio (middleNormalized d) < (19/5:ℝ)
  rw [hd]
  unfold middleRatio
  rw [hd]
  exact hbound

#print axioms solution
