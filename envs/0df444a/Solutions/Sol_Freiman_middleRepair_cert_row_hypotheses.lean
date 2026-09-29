-- Prove2me | solution 1 for Freiman.middleRepair_cert_row_hypotheses
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-10T10:07:04.188256+00:00
-- url     : https://prove2.me/submissions/1ae40ac6-b7e4-4a36-ae5f-793f4f7ede6f

import Definitions.Def_Freiman_middleRepairLedger
import Theorems.Thm_Freiman_middle_width_identity
import Theorems.Thm_Freiman_middle_continuant_growth
import Theorems.Thm_Freiman_prefixEval_difference
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.FinCases

open Freiman

namespace FreimanM8RowHyp20260910

set_option linter.unusedSimpArgs false

private theorem threshold_value (a x y : CertField) (u v : CertField) (r s : ℝ) :
    certThresholdVal (lowerHistoryThreshold a (x,y) (u,v)) r s =
      certFieldVal a * ((1+s*certFieldVal u)*(1+s*certFieldVal v)) /
        ((1+r*certFieldVal x)*(1+r*certFieldVal y)) := by
  unfold lowerHistoryThreshold lowerHistorySort
  split_ifs <;> simp only [certThresholdVal, certThresholdNum, certThresholdDen] <;> ring

private theorem field_alpha : certFieldVal lowerHistoryAlpha = middleAlpha := by
  norm_num [certFieldVal, lowerHistoryAlpha, middleAlpha]
  ring

private theorem field_beta : certFieldVal lowerHistoryBeta = middleBeta := by
  norm_num [certFieldVal, lowerHistoryBeta, middleBeta]
  ring

private theorem field_tau : certFieldVal lowerHistoryTau = middleRho := by
  norm_num [certFieldVal, lowerHistoryTau, middleRho]
  ring

private theorem field_rat (q : ℚ) : certFieldVal (lowerHistoryRat q) = q := by
  simp [certFieldVal, lowerHistoryRat]

private theorem cf23tau :
    certFieldVal (lowerHistoryCF [2,3] lowerHistoryTau) = prefixEval [2,3] middleRho := by
  norm_num [lowerHistoryCF, lowerHistoryMatrix, lowerHistoryDiv, lowerHistoryInv,
    certFieldVal, certFieldMul, certFieldAdd, certFieldScale, lowerHistoryRat,
    lowerHistoryTau, prefixEval, middleRho]
  have h3 : Real.sqrt (3:ℝ)^2 = 3 := Real.sq_sqrt (by norm_num)
  have hs : 0 ≤ Real.sqrt (3:ℝ) := Real.sqrt_nonneg _
  have h1 : Real.sqrt (3:ℝ)+2 ≠ 0 := by positivity
  have hd1 : 0 < 3 + (Real.sqrt (3:ℝ)-1) := by linarith
  have hd2 : 0 < 2 + 1/(3 + (Real.sqrt (3:ℝ)-1)) := by positivity
  field_simp [ne_of_gt hd1, ne_of_gt hd2]
  nlinarith


private theorem cf113tau :
    certFieldVal (lowerHistoryCF [1,1,3] lowerHistoryTau) = prefixEval [1,1,3] middleRho := by
  have hs : 1 < Real.sqrt (3:ℝ) := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hraw : 0 < Real.sqrt (3:ℝ) - 1 := by linarith
  have hs2 : Real.sqrt (3:ℝ)^2 = 3 := Real.sq_sqrt (by norm_num)
  have ht : 0 < (Real.sqrt (3:ℝ)-1) := by linarith
  have hd0 : 0 < (3 + (Real.sqrt (3:ℝ)-1)) := by positivity
  have hd1 : 0 < (1 + (1 / (3 + (Real.sqrt (3:ℝ)-1)))) := by positivity
  have hd2 : 0 < (1 + (1 / (1 + (1 / (3 + (Real.sqrt (3:ℝ)-1)))))) := by positivity
  norm_num [lowerHistoryCF, lowerHistoryMatrix, lowerHistoryDiv, lowerHistoryInv,
    certFieldVal, certFieldMul, certFieldAdd, certFieldScale, lowerHistoryRat,
    lowerHistoryTau, prefixEval, middleRho]
  field_simp (disch := positivity)
  nlinarith

private theorem cf112beta :
    certFieldVal (lowerHistoryCF [1,1,2] lowerHistoryBeta) = prefixEval [1,1,2] middleBeta := by
  have hs : 3 < Real.sqrt (21:ℝ) := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hraw : 0 < Real.sqrt (21:ℝ) - 3 := by linarith
  have hs2 : Real.sqrt (21:ℝ)^2 = 21 := Real.sq_sqrt (by norm_num)
  have ht : 0 < ((Real.sqrt (21:ℝ)-3)/2) := by linarith
  have hd0 : 0 < (2 + ((Real.sqrt (21:ℝ)-3)/2)) := by positivity
  have hd1 : 0 < (1 + (1 / (2 + ((Real.sqrt (21:ℝ)-3)/2)))) := by positivity
  have hd2 : 0 < (1 + (1 / (1 + (1 / (2 + ((Real.sqrt (21:ℝ)-3)/2)))))) := by positivity
  norm_num [lowerHistoryCF, lowerHistoryMatrix, lowerHistoryDiv, lowerHistoryInv,
    certFieldVal, certFieldMul, certFieldAdd, certFieldScale, lowerHistoryRat,
    lowerHistoryBeta, prefixEval, middleBeta]
  field_simp (disch := positivity)
  nlinarith

private theorem cf312beta :
    certFieldVal (lowerHistoryCF [3,1,2] lowerHistoryBeta) = prefixEval [3,1,2] middleBeta := by
  have hs : 3 < Real.sqrt (21:ℝ) := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hraw : 0 < Real.sqrt (21:ℝ) - 3 := by linarith
  have hs2 : Real.sqrt (21:ℝ)^2 = 21 := Real.sq_sqrt (by norm_num)
  have ht : 0 < ((Real.sqrt (21:ℝ)-3)/2) := by linarith
  have hd0 : 0 < (2 + ((Real.sqrt (21:ℝ)-3)/2)) := by positivity
  have hd1 : 0 < (1 + (1 / (2 + ((Real.sqrt (21:ℝ)-3)/2)))) := by positivity
  have hd2 : 0 < (3 + (1 / (1 + (1 / (2 + ((Real.sqrt (21:ℝ)-3)/2)))))) := by positivity
  norm_num [lowerHistoryCF, lowerHistoryMatrix, lowerHistoryDiv, lowerHistoryInv,
    certFieldVal, certFieldMul, certFieldAdd, certFieldScale, lowerHistoryRat,
    lowerHistoryBeta, prefixEval, middleBeta]
  field_simp (disch := positivity)
  nlinarith

private theorem cf3alpha :
    certFieldVal (lowerHistoryCF [3] lowerHistoryAlpha) = prefixEval [3] middleAlpha := by
  have hs : 3 < Real.sqrt (21:ℝ) := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hraw : 0 < Real.sqrt (21:ℝ) - 3 := by linarith
  have hs2 : Real.sqrt (21:ℝ)^2 = 21 := Real.sq_sqrt (by norm_num)
  have ht : 0 < ((Real.sqrt (21:ℝ)-3)/6) := by linarith
  have hd0 : 0 < (3 + ((Real.sqrt (21:ℝ)-3)/6)) := by positivity
  norm_num [lowerHistoryCF, lowerHistoryMatrix, lowerHistoryDiv, lowerHistoryInv,
    certFieldVal, certFieldMul, certFieldAdd, certFieldScale, lowerHistoryRat,
    lowerHistoryAlpha, prefixEval, middleAlpha]
  field_simp (disch := positivity)
  nlinarith

private theorem cf3beta :
    certFieldVal (lowerHistoryCF [3] lowerHistoryBeta) = prefixEval [3] middleBeta := by
  have hs : 3 < Real.sqrt (21:ℝ) := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hraw : 0 < Real.sqrt (21:ℝ) - 3 := by linarith
  have hs2 : Real.sqrt (21:ℝ)^2 = 21 := Real.sq_sqrt (by norm_num)
  have ht : 0 < ((Real.sqrt (21:ℝ)-3)/2) := by linarith
  have hd0 : 0 < (3 + ((Real.sqrt (21:ℝ)-3)/2)) := by positivity
  norm_num [lowerHistoryCF, lowerHistoryMatrix, lowerHistoryDiv, lowerHistoryInv,
    certFieldVal, certFieldMul, certFieldAdd, certFieldScale, lowerHistoryRat,
    lowerHistoryBeta, prefixEval, middleBeta]
  field_simp (disch := positivity)
  nlinarith

private theorem cf33alpha :
    certFieldVal (lowerHistoryCF [3,3] lowerHistoryAlpha) = prefixEval [3,3] middleAlpha := by
  have hs : 3 < Real.sqrt (21:ℝ) := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hraw : 0 < Real.sqrt (21:ℝ) - 3 := by linarith
  have hs2 : Real.sqrt (21:ℝ)^2 = 21 := Real.sq_sqrt (by norm_num)
  have ht : 0 < ((Real.sqrt (21:ℝ)-3)/6) := by linarith
  have hd0 : 0 < (3 + ((Real.sqrt (21:ℝ)-3)/6)) := by positivity
  have hd1 : 0 < (3 + (1 / (3 + ((Real.sqrt (21:ℝ)-3)/6)))) := by positivity
  norm_num [lowerHistoryCF, lowerHistoryMatrix, lowerHistoryDiv, lowerHistoryInv,
    certFieldVal, certFieldMul, certFieldAdd, certFieldScale, lowerHistoryRat,
    lowerHistoryAlpha, prefixEval, middleAlpha]
  field_simp (disch := positivity)
  nlinarith

private theorem cf33beta :
    certFieldVal (lowerHistoryCF [3,3] lowerHistoryBeta) = prefixEval [3,3] middleBeta := by
  have hs : 3 < Real.sqrt (21:ℝ) := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hraw : 0 < Real.sqrt (21:ℝ) - 3 := by linarith
  have hs2 : Real.sqrt (21:ℝ)^2 = 21 := Real.sq_sqrt (by norm_num)
  have ht : 0 < ((Real.sqrt (21:ℝ)-3)/2) := by linarith
  have hd0 : 0 < (3 + ((Real.sqrt (21:ℝ)-3)/2)) := by positivity
  have hd1 : 0 < (3 + (1 / (3 + ((Real.sqrt (21:ℝ)-3)/2)))) := by positivity
  norm_num [lowerHistoryCF, lowerHistoryMatrix, lowerHistoryDiv, lowerHistoryInv,
    certFieldVal, certFieldMul, certFieldAdd, certFieldScale, lowerHistoryRat,
    lowerHistoryBeta, prefixEval, middleBeta]
  field_simp (disch := positivity)
  nlinarith


private theorem a_value (t : ℚ) (r s : ℝ) :
    certThresholdVal (middleCertA t) r s = middleScalarA r s t := by
  unfold middleCertA middleScalarA middleScalarThreshold
  rw [threshold_value, field_rat, field_beta, cf23tau, cf113tau, cf112beta]

private theorem b_value (t : ℚ) (r s : ℝ) :
    certThresholdVal (middleCertB t) r s = middleScalarB r s t := by
  unfold middleCertB middleScalarB middleScalarThreshold
  rw [threshold_value, field_rat, cf312beta, cf3alpha, cf23tau, cf113tau]

private theorem scale_value (t : ℚ) (h : CertThreshold) (r s : ℝ) :
    certThresholdVal (lowerHistoryScaleThreshold t h) r s = (t:ℝ)*certThresholdVal h r s := by
  simp only [lowerHistoryScaleThreshold, certThresholdVal, certThresholdNum, certThresholdDen,
    certFieldScale, certFieldVal]
  push_cast
  ring

private theorem wh0 : lowerHistoryWH ([],[]) = lowerHistoryThreshold (lowerHistoryRat 1)
    (lowerHistoryAlpha,lowerHistoryBeta) (lowerHistoryAlpha,lowerHistoryBeta)  := by
  norm_num [lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryAbs,
    lowerHistoryDiv, lowerHistoryInv, lowerHistorySign, lowerHistoryQuadSign,
    lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryThreshold, lowerHistorySort,
    lowerHistoryLex, lowerHistoryRat, lowerHistoryAlpha, lowerHistoryBeta,
    certFieldAdd, certFieldSub, certFieldMul, certFieldScale]

private theorem wh3 : lowerHistoryWH ([3],[3]) = lowerHistoryThreshold (lowerHistoryRat 1)
    (lowerHistoryCF [3] lowerHistoryAlpha,lowerHistoryCF [3] lowerHistoryBeta)
    (lowerHistoryCF [3] lowerHistoryAlpha,lowerHistoryCF [3] lowerHistoryBeta)  := by
  norm_num [lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryAbs,
    lowerHistoryDiv, lowerHistoryInv, lowerHistorySign, lowerHistoryQuadSign,
    lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryThreshold, lowerHistorySort,
    lowerHistoryLex, lowerHistoryRat, lowerHistoryAlpha, lowerHistoryBeta,
    certFieldAdd, certFieldSub, certFieldMul, certFieldScale]

private theorem wh33 : lowerHistoryWH ([3,3],[3,3]) = lowerHistoryThreshold (lowerHistoryRat 1)
    (lowerHistoryCF [3,3] lowerHistoryAlpha,lowerHistoryCF [3,3] lowerHistoryBeta)
    (lowerHistoryCF [3,3] lowerHistoryAlpha,lowerHistoryCF [3,3] lowerHistoryBeta)  := by
  norm_num [lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryAbs,
    lowerHistoryDiv, lowerHistoryInv, lowerHistorySign, lowerHistoryQuadSign,
    lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryThreshold, lowerHistorySort,
    lowerHistoryLex, lowerHistoryRat, lowerHistoryAlpha, lowerHistoryBeta,
    certFieldAdd, certFieldSub, certFieldMul, certFieldScale]

private theorem wh0_value (r s : ℝ) : certThresholdVal (lowerHistoryWH ([],[])) r s =
    middleH r s middleAlpha middleBeta := by
  rw [wh0, threshold_value, field_rat, field_alpha, field_beta]
  norm_num [middleH]

private theorem wh3_value (r s : ℝ) : certThresholdVal (lowerHistoryWH ([3],[3])) r s =
    middleH r s (prefixEval [3] middleAlpha) (prefixEval [3] middleBeta) := by
  rw [wh3, threshold_value, field_rat, cf3alpha, cf3beta]
  norm_num [middleH]

private theorem wh33_value (r s : ℝ) : certThresholdVal (lowerHistoryWH ([3,3],[3,3])) r s =
    middleH r s (prefixEval [3,3] middleAlpha) (prefixEval [3,3] middleBeta) := by
  rw [wh33, threshold_value, field_rat, cf33alpha, cf33beta]
  norm_num [middleH]

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


private theorem q_pos (c : MiddleCore) : 0 < middleQ c := by
  have hl := (middle_continuant_growth (middleNormalized c).left).2.1
  have hr := (middle_continuant_growth (middleNormalized c).right).2.1
  exact div_pos (sq_pos_of_pos hl) (sq_pos_of_pos hr)

private theorem normalized_width_order (c : MiddleCore) :
    middleWidth (middleNormalized c).right ≤ middleWidth (middleNormalized c).left := by
  unfold middleNormalized
  split_ifs with h
  · exact h
  · exact le_of_lt (lt_of_not_ge h)

private theorem ratio0 (c : MiddleCore) : middleRatio c =
    middleH (middleParameter (middleNormalized c).left) (middleParameter (middleNormalized c).right)
      middleAlpha middleBeta / middleQ c := by
  simpa only [List.append_nil, prefixEval, middleRatio, middleQ] using
    ratio_append (middleNormalized c).left (middleNormalized c).right []

private theorem normal_holds (c : MiddleCore) :
    certBoundHolds ⟨false,false,lowerHistoryWH ([],[])⟩
      (middleParameter (middleNormalized c).left) (middleParameter (middleNormalized c).right) (middleQ c) := by
  change middleQ c ≤ certThresholdVal (lowerHistoryWH ([],[])) _ _
  rw [wh0_value]
  have h : 1 ≤ middleRatio c := by
    apply (le_div_iff₀ (width_pos (middleNormalized c).right)).2
    simpa only [one_mul] using normalized_width_order c
  rw [ratio0] at h
  have hh := (le_div_iff₀ (q_pos c)).mp h
  simpa only [one_mul] using hh

private theorem a_holds (c : MiddleCore) (q : ℚ) :
    certBoundHolds ⟨true,true,middleCertA q⟩
      (middleParameter (middleNormalized c).left) (middleParameter (middleNormalized c).right) (middleQ c) ↔
    middleA c q < middleQ c := by
  change certThresholdVal (middleCertA q) _ _ < middleQ c ↔ _
  rw [a_value]
  rfl

private theorem b_holds (c : MiddleCore) (q : ℚ) :
    certBoundHolds ⟨false,true,middleCertB q⟩
      (middleParameter (middleNormalized c).left) (middleParameter (middleNormalized c).right) (middleQ c) ↔
    middleQ c < middleB c q := by
  change middleQ c < certThresholdVal (middleCertB q) _ _ ↔ _
  rw [b_value]
  rfl

private theorem short_holds (c : MiddleCore) (n : ℕ)
    (heval : ∀ p s : ℝ, certThresholdVal (lowerHistoryWH (List.replicate n 3,List.replicate n 3)) p s =
      middleH p s (prefixEval (List.replicate n 3) middleAlpha) (prefixEval (List.replicate n 3) middleBeta)) :
    certBoundHolds ⟨true,false,lowerHistoryScaleThreshold (5/7)
        (lowerHistoryWH (List.replicate n 3,List.replicate n 3))⟩
      (middleParameter (middleNormalized c).left) (middleParameter (middleNormalized c).right) (middleQ c) ↔
    middleShort c n := by
  change certThresholdVal (lowerHistoryScaleThreshold (5/7)
      (lowerHistoryWH (List.replicate n 3,List.replicate n 3))) _ _ ≤ middleQ c ↔ _
  rw [scale_value, heval]
  norm_num only [Rat.cast_div, Rat.cast_ofNat]
  let X := middleWidth ((middleNormalized c).left++List.replicate n 3)
  let Y := middleWidth ((middleNormalized c).right++List.replicate n 3)
  have hY : 0 < Y := width_pos _
  have hq := q_pos c
  have hr := ratio_append (middleNormalized c).left (middleNormalized c).right (List.replicate n 3)
  change X/Y = _/middleQ c at hr
  change _ ↔ X ≤ (7/5:ℝ)*Y
  rw [← div_le_iff₀ hY, hr, div_le_iff₀ hq]
  constructor <;> intro h <;> nlinarith only [h]

private theorem short1_holds (c : MiddleCore) :
    certBoundHolds ⟨true,false,lowerHistoryScaleThreshold (5/7) (lowerHistoryWH ([3],[3]))⟩
      (middleParameter (middleNormalized c).left) (middleParameter (middleNormalized c).right) (middleQ c) ↔
    middleShort c 1 := by
  simpa only [List.replicate_succ, List.replicate_zero] using short_holds c 1
    (by simpa only [List.replicate_succ, List.replicate_zero] using wh3_value)

private theorem short2_holds (c : MiddleCore) :
    certBoundHolds ⟨true,false,lowerHistoryScaleThreshold (5/7) (lowerHistoryWH ([3,3],[3,3]))⟩
      (middleParameter (middleNormalized c).left) (middleParameter (middleNormalized c).right) (middleQ c) ↔
    middleShort c 2 := by
  simpa only [List.replicate_succ, List.replicate_zero] using short_holds c 2
    (by simpa only [List.replicate_succ, List.replicate_zero] using wh33_value)

private theorem uniform_holds (c : MiddleCore) :
    certBoundHolds ⟨true,true,lowerHistoryScaleThreshold (5/19) (lowerHistoryWH ([],[]))⟩
      (middleParameter (middleNormalized c).left) (middleParameter (middleNormalized c).right) (middleQ c) ↔
    middleRatio c < (19/5:ℝ) := by
  change certThresholdVal (lowerHistoryScaleThreshold (5/19) (lowerHistoryWH ([],[]))) _ _ < middleQ c ↔ _
  rw [scale_value, wh0_value, ratio0, div_lt_iff₀ (q_pos c)]
  norm_num only [Rat.cast_div, Rat.cast_ofNat]
  constructor <;> intro h <;> nlinarith only [h]

private theorem complement_holds (b : CertBound) (p s q : ℝ) :
    certBoundHolds (lowerHistoryComplement b) p s q ↔ ¬ certBoundHolds b p s q := by
  rcases b with ⟨bl, bs, bt⟩
  cases bl <;> cases bs <;> simp [lowerHistoryComplement, certBoundHolds, not_le, not_lt]

end FreimanM8RowHyp20260910

open FreimanM8RowHyp20260910

theorem solution :
    ∀ (c : MiddleCore) (f : Fin 11), middleRepairCertDomain c f.val → decide ((middleNormalized c).left.length%2 ≠ (middleNormalized c).right.length%2) = middleCertParity f.val ∧ middleCertHolds (middleCertFamilyHyp f.val) (middleParameter (middleNormalized c).left) (middleParameter (middleNormalized c).right) (middleQ c) := by
  intro c f h
  fin_cases f <;>
    simp [middleRepairCertDomain, middleCertRow, middleRowCondition, middleCertParity] at h <;>
    simp [middleCertParity, middleCertFamilyHyp, middleCertHolds, complement_holds,
      normal_holds, a_holds, b_holds, short1_holds, short2_holds, uniform_holds] <;>
    aesop

#print axioms solution


