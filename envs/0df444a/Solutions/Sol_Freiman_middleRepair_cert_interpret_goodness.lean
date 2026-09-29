-- Prove2me | solution 1 for Freiman.middleRepair_cert_interpret_goodness
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-10T10:28:34.003192+00:00
-- url     : https://prove2.me/submissions/9feb7739-4650-49da-9718-23cc3f96d7fb

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
import Mathlib.Tactic.Tauto

open Freiman

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

namespace M8Sep10InterpretGoodness

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


private theorem q_pos (c : MiddleCore) : 0 < middleQ c := by
  have hl := (middle_continuant_growth (middleNormalized c).left).2.1
  have hr := (middle_continuant_growth (middleNormalized c).right).2.1
  exact div_pos (sq_pos_of_pos hl) (sq_pos_of_pos hr)

private theorem cf_short (w : List ℕ+) (hw : w ∈ ([[],[1],[2],[3]] : List (List ℕ+))) :
    certFieldVal (lowerHistoryCF w lowerHistoryAlpha) = prefixEval w middleAlpha ∧
    certFieldVal (lowerHistoryCF w lowerHistoryBeta) = prefixEval w middleBeta := by
  have hs : 3 < Real.sqrt (21:ℝ) := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hs2 : Real.sqrt (21:ℝ)^2 = 21 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt (21:ℝ)-3 := by linarith
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · constructor <;> norm_num [lowerHistoryCF, lowerHistoryMatrix, lowerHistoryDiv, lowerHistoryInv, certFieldVal, certFieldMul, certFieldAdd, certFieldScale, lowerHistoryRat, lowerHistoryAlpha, lowerHistoryBeta, prefixEval, middleAlpha, middleBeta] <;>
      field_simp (disch := positivity) <;> nlinarith
  · constructor <;> norm_num [lowerHistoryCF, lowerHistoryMatrix, lowerHistoryDiv, lowerHistoryInv, certFieldVal, certFieldMul, certFieldAdd, certFieldScale, lowerHistoryRat, lowerHistoryAlpha, lowerHistoryBeta, prefixEval, middleAlpha, middleBeta] <;>
      field_simp (disch := positivity) <;> nlinarith
  · constructor <;> norm_num [lowerHistoryCF, lowerHistoryMatrix, lowerHistoryDiv, lowerHistoryInv, certFieldVal, certFieldMul, certFieldAdd, certFieldScale, lowerHistoryRat, lowerHistoryAlpha, lowerHistoryBeta, prefixEval, middleAlpha, middleBeta] <;>
      field_simp (disch := positivity) <;> nlinarith
  · constructor <;> norm_num [lowerHistoryCF, lowerHistoryMatrix, lowerHistoryDiv, lowerHistoryInv, certFieldVal, certFieldMul, certFieldAdd, certFieldScale, lowerHistoryRat, lowerHistoryAlpha, lowerHistoryBeta, prefixEval, middleAlpha, middleBeta] <;>
      field_simp (disch := positivity) <;> nlinarith

private def rowPairs : List LowerPair :=
  [([],[1]),([1],[]),([3],[]),([2],[]),([3],[1]),([3],[2]),([2],[3]),([2],[2]),([3],[3])]

private theorem wh_coefficient (w : LowerPair) (hw : w ∈ rowPairs) :
    certFieldVal (lowerHistoryAbs (lowerHistoryDiv
      (certFieldSub (lowerHistoryCF w.1 lowerHistoryAlpha) (lowerHistoryCF w.1 lowerHistoryBeta))
      (certFieldSub (lowerHistoryCF w.2 lowerHistoryAlpha) (lowerHistoryCF w.2 lowerHistoryBeta)))) =
    middleWidth w.1 / middleWidth w.2 := by
  have hs : 3 < Real.sqrt (21:ℝ) := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hs2 : Real.sqrt (21:ℝ)^2 = 21 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt (21:ℝ)-3 := by linarith
  have hab : 0 < middleBeta-middleAlpha := sub_pos.mpr ab_unit.2.2
  have ha : 0 ≤ middleAlpha := ab_unit.1.1
  have hb : 0 ≤ middleBeta := ab_unit.2.1.1
  simp only [rowPairs, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [middle_width_identity]
    norm_num [lowerHistoryCF, lowerHistoryMatrix, lowerHistoryAbs, lowerHistoryDiv, lowerHistoryInv, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryRat, lowerHistoryAlpha, lowerHistoryBeta, certFieldAdd, certFieldSub, certFieldMul, certFieldScale, certFieldVal, middleCD, middleParameter]
    dsimp only [middleAlpha, middleBeta] at hab ha hb ⊢
    field_simp (disch := positivity)
    all_goals nlinarith
  · simp only [middle_width_identity]
    norm_num [lowerHistoryCF, lowerHistoryMatrix, lowerHistoryAbs, lowerHistoryDiv, lowerHistoryInv, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryRat, lowerHistoryAlpha, lowerHistoryBeta, certFieldAdd, certFieldSub, certFieldMul, certFieldScale, certFieldVal, middleCD, middleParameter]
    dsimp only [middleAlpha, middleBeta] at hab ha hb ⊢
    field_simp (disch := positivity)
    all_goals nlinarith
  · simp only [middle_width_identity]
    norm_num [lowerHistoryCF, lowerHistoryMatrix, lowerHistoryAbs, lowerHistoryDiv, lowerHistoryInv, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryRat, lowerHistoryAlpha, lowerHistoryBeta, certFieldAdd, certFieldSub, certFieldMul, certFieldScale, certFieldVal, middleCD, middleParameter]
    dsimp only [middleAlpha, middleBeta] at hab ha hb ⊢
    field_simp (disch := positivity)
    all_goals nlinarith
  · simp only [middle_width_identity]
    norm_num [lowerHistoryCF, lowerHistoryMatrix, lowerHistoryAbs, lowerHistoryDiv, lowerHistoryInv, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryRat, lowerHistoryAlpha, lowerHistoryBeta, certFieldAdd, certFieldSub, certFieldMul, certFieldScale, certFieldVal, middleCD, middleParameter]
    dsimp only [middleAlpha, middleBeta] at hab ha hb ⊢
    field_simp (disch := positivity)
    all_goals nlinarith
  · simp only [middle_width_identity]
    norm_num [lowerHistoryCF, lowerHistoryMatrix, lowerHistoryAbs, lowerHistoryDiv, lowerHistoryInv, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryRat, lowerHistoryAlpha, lowerHistoryBeta, certFieldAdd, certFieldSub, certFieldMul, certFieldScale, certFieldVal, middleCD, middleParameter]
    dsimp only [middleAlpha, middleBeta] at hab ha hb ⊢
    field_simp (disch := positivity)
    all_goals nlinarith
  · simp only [middle_width_identity]
    norm_num [lowerHistoryCF, lowerHistoryMatrix, lowerHistoryAbs, lowerHistoryDiv, lowerHistoryInv, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryRat, lowerHistoryAlpha, lowerHistoryBeta, certFieldAdd, certFieldSub, certFieldMul, certFieldScale, certFieldVal, middleCD, middleParameter]
    dsimp only [middleAlpha, middleBeta] at hab ha hb ⊢
    field_simp (disch := positivity)
    all_goals nlinarith
  · simp only [middle_width_identity]
    norm_num [lowerHistoryCF, lowerHistoryMatrix, lowerHistoryAbs, lowerHistoryDiv, lowerHistoryInv, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryRat, lowerHistoryAlpha, lowerHistoryBeta, certFieldAdd, certFieldSub, certFieldMul, certFieldScale, certFieldVal, middleCD, middleParameter]
    dsimp only [middleAlpha, middleBeta] at hab ha hb ⊢
    field_simp (disch := positivity)
    all_goals nlinarith
  · simp only [middle_width_identity]
    norm_num [lowerHistoryCF, lowerHistoryMatrix, lowerHistoryAbs, lowerHistoryDiv, lowerHistoryInv, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryRat, lowerHistoryAlpha, lowerHistoryBeta, certFieldAdd, certFieldSub, certFieldMul, certFieldScale, certFieldVal, middleCD, middleParameter]
    dsimp only [middleAlpha, middleBeta] at hab ha hb ⊢
    field_simp (disch := positivity)
  · simp only [middle_width_identity]
    norm_num [lowerHistoryCF, lowerHistoryMatrix, lowerHistoryAbs, lowerHistoryDiv, lowerHistoryInv, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryRat, lowerHistoryAlpha, lowerHistoryBeta, certFieldAdd, certFieldSub, certFieldMul, certFieldScale, certFieldVal, middleCD, middleParameter]
    dsimp only [middleAlpha, middleBeta] at hab ha hb ⊢
    field_simp (disch := positivity)


private theorem wh_value (w : LowerPair) (hw : w ∈ rowPairs) (r s : ℝ) :
    certThresholdVal (lowerHistoryWH w) r s =
      (middleWidth w.1 / middleWidth w.2) *
        ((1+s*prefixEval w.2 middleAlpha)*(1+s*prefixEval w.2 middleBeta)) /
        ((1+r*prefixEval w.1 middleAlpha)*(1+r*prefixEval w.1 middleBeta)) := by
  have hshort : w.1 ∈ ([[],[1],[2],[3]] : List (List ℕ+)) ∧
      w.2 ∈ ([[],[1],[2],[3]] : List (List ℕ+)) := by
    simp only [rowPairs, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  unfold lowerHistoryWH
  rw [threshold_value, wh_coefficient w hw, (cf_short w.1 hshort.1).1,
    (cf_short w.1 hshort.1).2, (cf_short w.2 hshort.2).1, (cf_short w.2 hshort.2).2]

private theorem ratio_pair (u v : List ℕ+) (w : LowerPair) (hw : w ∈ rowPairs) :
    middleWidth (u++w.1) / middleWidth (v++w.2) =
      certThresholdVal (lowerHistoryWH w) (middleParameter u) (middleParameter v) /
        ((middleCD u).2^2 / (middleCD v).2^2) := by
  have hu := middle_continuant_growth u
  have hv := middle_continuant_growth v
  have hup := hu.1
  have hvp := hv.1
  have hud := hu.2.1
  have hvd := hv.2.1
  have ha1 := (pe_unit w.1 middleAlpha ab_unit.1).1
  have hb1 := (pe_unit w.1 middleBeta ab_unit.2.1).1
  have ha2 := (pe_unit w.2 middleAlpha ab_unit.1).1
  have hb2 := (pe_unit w.2 middleBeta ab_unit.2.1).1
  have hw1 := width_pos w.1
  have hw2 := width_pos w.2
  rw [width_append, width_append, wh_value w hw]
  field_simp (disch := positivity)

private theorem width_holds (c : MiddleCore) (w : LowerPair) (hw : w ∈ rowPairs) :
    middleWidth ((middleNormalized c).right++w.2) ≤ middleWidth ((middleNormalized c).left++w.1) ↔
      middleCertHolds [⟨false,false,lowerHistoryWH w⟩]
        (middleParameter (middleNormalized c).left) (middleParameter (middleNormalized c).right) (middleQ c) := by
  calc
    _ ↔ 1 ≤ middleWidth ((middleNormalized c).left++w.1) /
        middleWidth ((middleNormalized c).right++w.2) := by
      rw [le_div_iff₀ (width_pos _), one_mul]
    _ ↔ 1 ≤ certThresholdVal (lowerHistoryWH w)
        (middleParameter (middleNormalized c).left) (middleParameter (middleNormalized c).right) / middleQ c := by
      rw [ratio_pair _ _ w hw]
      rfl
    _ ↔ middleQ c ≤ certThresholdVal (lowerHistoryWH w)
        (middleParameter (middleNormalized c).left) (middleParameter (middleNormalized c).right) := by
      rw [le_div_iff₀ (q_pos c), one_mul]
    _ ↔ _ := by simp [middleCertHolds, certBoundHolds]

private theorem select_side (c : MiddleCore) (w : LowerPair) (hw : w ∈ rowPairs) :
    ∃ side : Bool,
      middleRepairChild c w.1 w.2 = middleRepairAct side (middleRepairRawChild c w.1 w.2) ∧
      middleCertHolds [if side then ⟨true,true,lowerHistoryWH w⟩ else ⟨false,false,lowerHistoryWH w⟩]
        (middleParameter (middleNormalized c).left) (middleParameter (middleNormalized c).right) (middleQ c) := by
  by_cases hh : middleWidth ((middleNormalized c).right++w.2) ≤ middleWidth ((middleNormalized c).left++w.1)
  · refine ⟨false, ?_, ?_⟩
    · change middleNormalized (middleRepairRawChild c w.1 w.2) = middleRepairRawChild c w.1 w.2
      unfold middleNormalized
      exact if_pos hh
    · simpa only [Bool.false_eq_true, ↓reduceIte] using (width_holds c w hw).mp hh
  · refine ⟨true, ?_, ?_⟩
    · change middleNormalized (middleRepairRawChild c w.1 w.2) = middleRepairSwap (middleRepairRawChild c w.1 w.2)
      unfold middleNormalized
      exact if_neg hh
    · have hn := mt (width_holds c w hw).mpr hh
      simpa [middleCertHolds, certBoundHolds, not_le] using hn


theorem normalized_idem (c : MiddleCore) :
    middleNormalized (middleNormalized c) = middleNormalized c := by
  unfold middleNormalized
  split_ifs <;> first | rfl | (simp_all only [not_le]; order)

theorem bounds_normalized (c : MiddleCore) : middleBounds (middleNormalized c) = middleBounds c := by
  simp only [middleBounds, normalized_idem]

theorem row_children_as_pairs (c : MiddleCore) (f : Fin 9) :
    middleRepairRowChildren c (middleCertRow f.val) =
      (middleCertChildren f.val).map (fun w => middleRepairChild c w.1 w.2) := by
  fin_cases f <;> simp [middleRepairRowChildren, middleCertRow, middleCertChildren,
    middleRepairJ, List.replicate_succ, List.replicate_zero]

theorem row_pair_digits (f : Fin 9) :
    ∀ w ∈ middleCertChildren f.val,
      middleDigits123 w.1 ∧ middleDigits123 w.2 ∧ 0 < w.1.length+w.2.length := by
  fin_cases f <;> simp [middleCertChildren, middleDigits123]

theorem domain_parity (c : MiddleCore) (f : Fin 9) (hd : middleRepairCertDomain c f.val) :
    decide ((middleNormalized c).left.length%2 ≠ (middleNormalized c).right.length%2) =
      middleCertParity f.val := by
  fin_cases f <;>
    norm_num [middleRepairCertDomain, middleRowCondition, middleCertRow, middleCertParity] at hd ⊢ <;>
    tauto


private theorem extend_bounds (c : MiddleCore) (w : LowerPair) (side : Bool)
    (hn : middleRepairChild c w.1 w.2 = middleRepairAct side (middleRepairRawChild c w.1 w.2))
    (a : ℕ+) :
    middleBounds (middleRepairAct side (middleRepairRawChild c
      (lowerHistorySet w side (lowerHistoryPick w side++[a])).1
      (lowerHistorySet w side (lowerHistoryPick w side++[a])).2)) =
      middleBounds (middleRepairChild (middleRepairChild c w.1 w.2) [a] []) := by
  have hi : middleNormalized (middleRepairChild c w.1 w.2) =
      middleRepairAct side (middleRepairRawChild c w.1 w.2) := by
    simpa only [middleRepairChild, normalized_idem] using hn
  conv_rhs => rw [middleRepairChild, bounds_normalized]
  unfold middleRepairRawChild
  rw [hi]
  cases side <;> simp [middleRepairAct, middleRepairSwap, middleRepairRawChild, lowerHistorySet,
    lowerHistoryPick, List.append_assoc]

private theorem child_parity (c : MiddleCore) (w : LowerPair) (side parity : Bool)
    (hn : middleRepairChild c w.1 w.2 = middleRepairAct side (middleRepairRawChild c w.1 w.2))
    (hp : decide ((middleNormalized c).left.length%2 ≠ (middleNormalized c).right.length%2) = parity) :
    decide ((middleNormalized (middleRepairChild c w.1 w.2)).left.length%2=1) =
      xor (decide ((middleNormalized c).left.length%2=1)) (middleCertOdd w parity side) := by
  have hi : middleNormalized (middleRepairChild c w.1 w.2) =
      middleRepairAct side (middleRepairRawChild c w.1 w.2) := by
    simpa only [middleRepairChild, normalized_idem] using hn
  rw [hi, ← hp]
  cases side <;>
    simp only [middleRepairAct, middleRepairSwap, middleRepairRawChild, Bool.false_eq_true, ↓reduceIte,
      List.length_append, middleCertOdd, lowerHistoryPick, Bool.and_false, Bool.and_true,
      Bool.false_xor] <;>
    by_cases hl : (middleNormalized c).left.length%2=1 <;>
    by_cases hr : (middleNormalized c).right.length%2=1 <;>
    by_cases hw : w.1.length%2=1 <;>
    by_cases hv : w.2.length%2=1 <;>
    simp_all <;> omega

private def goodSpec (w : LowerPair) (k : ℕ) (parity side : Bool) : MiddleCertSpec :=
  let one := lowerHistorySet w side (lowerHistoryPick w side++[1])
  let two := lowerHistorySet w side (lowerHistoryPick w side++[2])
  let ordered := if middleCertOdd w parity side then (one,two) else (two,one)
  ⟨.good k side,ordered.1,true,ordered.2,false,
    [if side then ⟨true,true,lowerHistoryWH w⟩ else ⟨false,false,lowerHistoryWH w⟩]⟩

private theorem good_from_spec
    (hcriterion : ∀ c : MiddleCore, middleRegular c →
      (middleRepairGood c ↔ (if (middleNormalized c).left.length%2=0
        then (middleBounds (middleRepairChild c [1] [])).1 ≤ (middleBounds (middleRepairChild c [2] [])).2
        else (middleBounds (middleRepairChild c [2] [])).1 ≤ (middleBounds (middleRepairChild c [1] [])).2)))
    (c : MiddleCore) (w : LowerPair) (k : ℕ) (parity side : Bool)
    (hr : middleRegular (middleRepairChild c w.1 w.2))
    (hn : middleRepairChild c w.1 w.2 = middleRepairAct side (middleRepairRawChild c w.1 w.2))
    (hp : decide ((middleNormalized c).left.length%2 ≠ (middleNormalized c).right.length%2) = parity)
    (hh : middleCertHolds [if side then ⟨true,true,lowerHistoryWH w⟩ else ⟨false,false,lowerHistoryWH w⟩]
      (middleParameter (middleNormalized c).left) (middleParameter (middleNormalized c).right) (middleQ c))
    (hs : middleRepairCertSpecHolds c (goodSpec w k parity side)) :
    middleRepairGood (middleRepairChild c w.1 w.2) := by
  apply (hcriterion _ hr).2
  have he := hs hh
  have hpar := child_parity c w side parity hn hp
  have he1 := extend_bounds c w side hn 1
  have he2 := extend_bounds c w side hn 2
  change middleBounds (middleRepairAct side (MiddleCore.mk _ _)) = _ at he1 he2
  change middleRepairCertEndpoint c _ false side ≤ middleRepairCertEndpoint c _ true side at he
  unfold goodSpec at he
  dsimp only at he
  unfold middleRepairCertEndpoint at he
  by_cases ho : middleCertOdd w parity side = true <;>
    by_cases hc : (middleNormalized c).left.length%2=0 <;>
    simp only [ho, hc, ↓reduceIte, Bool.false_eq_true, he1, he2, neg_le_neg_iff] at he
  · have hchild : (middleNormalized (middleRepairChild c w.1 w.2)).left.length%2≠0 := by
      simp only [ho, Bool.xor_true] at hpar
      have hl : (middleNormalized c).left.length%2≠1 := by omega
      simp only [hl, decide_false, Bool.not_false, decide_eq_true_eq] at hpar
      omega
    simpa only [hchild, ↓reduceIte] using he
  · have hchild : (middleNormalized (middleRepairChild c w.1 w.2)).left.length%2=0 := by
      have hl : (middleNormalized c).left.length%2=1 := by omega
      simp only [ho, hl, decide_true, Bool.true_xor, Bool.not_true, decide_eq_false_iff_not] at hpar
      omega
    simpa only [hchild, ↓reduceIte] using he
  · have hchild : (middleNormalized (middleRepairChild c w.1 w.2)).left.length%2=0 := by
      have ho' : middleCertOdd w parity side = false := Bool.eq_false_iff.mpr ho
      have hl : (middleNormalized c).left.length%2≠1 := by omega
      simp only [ho', hl, decide_false, Bool.xor_false, decide_eq_false_iff_not] at hpar
      omega
    simpa only [hchild, ↓reduceIte] using he
  · have hchild : (middleNormalized (middleRepairChild c w.1 w.2)).left.length%2≠0 := by
      have ho' : middleCertOdd w parity side = false := Bool.eq_false_iff.mpr ho
      have hl : (middleNormalized c).left.length%2=1 := by omega
      simp only [ho', hl, decide_true, Bool.xor_false, decide_eq_true_eq] at hpar
      omega
    simpa only [hchild, ↓reduceIte] using he


private theorem good_spec_member (f : Fin 9) (w : LowerPair) (hw : w ∈ middleCertChildren f.val) :
    ∃ k : ℕ, ∀ side : Bool, goodSpec w k (middleCertParity f.val) side ∈ middleCertSpecs f.val := by
  obtain ⟨k,hk⟩ := List.mem_iff_getElem?.mp hw
  refine ⟨k, ?_⟩
  intro side
  have hf : ¬9 ≤ f.val := by omega
  simp only [middleCertSpecs, hf, ↓reduceIte, List.mem_append, List.mem_flatMap]
  left
  left
  right
  refine ⟨(w,k), List.mk_mem_zipIdx_iff_getElem?.mpr hk, ?_⟩
  simp only [List.mem_cons, List.mem_map]
  right
  refine ⟨(side, if side then ⟨true,true,lowerHistoryWH w⟩ else ⟨false,false,lowerHistoryWH w⟩), ?_, ?_⟩
  · cases side <;> simp [middleCertNormals]
  · rfl


private theorem row_pair_mem (f : Fin 9) (w : LowerPair) (hw : w ∈ middleCertChildren f.val) :
    w ∈ rowPairs := by
  fin_cases f <;>
    simp only [middleCertChildren, rowPairs, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢ <;>
    tauto

end M8Sep10InterpretGoodness

open M8Sep10InterpretGoodness

theorem solution :
    (∀ c : MiddleCore, middleRegular c → (middleRepairGood c ↔ (if (middleNormalized c).left.length%2=0 then (middleBounds (middleRepairChild c [1] [])).1 ≤ (middleBounds (middleRepairChild c [2] [])).2 else (middleBounds (middleRepairChild c [2] [])).1 ≤ (middleBounds (middleRepairChild c [1] [])).2))) → (∀ (c : MiddleCore) (u v : List ℕ+), middleRegular c → middleDigits123 u → middleDigits123 v →
      0 < u.length+v.length → middleRegular (middleRepairChild c u v) ∧ middleRepairProper c (middleRepairChild c u v)) → (∀ c : MiddleCore, middleRegular c → (middleBounds c).1 ≤ (middleBounds c).2) → ∀ (c : MiddleCore) (f : Fin 9), middleRepairCertDomain c f.val → middleRepairCertActualFamily c f.val → ∀ d ∈ middleRepairRowChildren c (middleCertRow f.val), middleRepairGood d := by
  intro hcriterion hchild _horder c f hd ha d hm
  rw [row_children_as_pairs c f] at hm
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
  have hdigits := row_pair_digits f w hw
  have hr := (hchild c w.1 w.2 hd.1 hdigits.1 hdigits.2.1 hdigits.2.2).1
  obtain ⟨side,hn,hh⟩ := select_side c w (row_pair_mem f w hw)
  obtain ⟨k,hk⟩ := good_spec_member f w hw
  exact good_from_spec hcriterion c w k (middleCertParity f.val) side hr hn
    (domain_parity c f hd) hh (ha _ (hk side))

#print axioms solution
