-- Prove2me | solution 1 for Freiman.late_equal_endpoint_from_width_cf
-- status  : ACCEPTED   (prove)
-- author  : @Koki Yamada
-- created : 2026-09-16T04:47:25.697113+00:00
-- url     : https://prove2.me/submissions/0266ddff-ebc5-4d53-9bee-58dc41907660

import Definitions.Def_Freiman_lateGeometry
import Theorems.Thm_Freiman_lowerHistory_cf_value
import Theorems.Thm_Freiman_lowerHistory_inv_value
import Theorems.Thm_Freiman_lowerHistory_sign_value
import Theorems.Thm_Freiman_lowerHistory_width_threshold
import Theorems.Thm_Freiman_prefixEval_difference
import Theorems.Thm_Freiman_continuant_denominator_pos
import Mathlib.Tactic


open Freiman
namespace M7ScaledCut14

private theorem pe_append (u v : List ℕ+) (x : ℝ) :
    prefixEval (u ++ v) x = prefixEval u (prefixEval v x) := by
  induction u with
  | nil => rfl
  | cons a u ih => simp only [List.cons_append, prefixEval, ih]

private theorem pe_icc (w : List ℕ+) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    prefixEval w x ∈ Set.Icc (0 : ℝ) 1 := by
  induction w with
  | nil => exact hx
  | cons a w ih =>
    have ha : (1 : ℝ) ≤ (a : ℕ) := by exact_mod_cast a.pos
    have hnn : 0 ≤ prefixEval w x := ih.1
    simp only [prefixEval, Set.mem_Icc]
    constructor
    · positivity
    · apply (div_le_one (by linarith [ih.1])).2
      linarith [ih.1]

private theorem cd_eq (w : List ℕ+) :
    lowerCD w = (wordContinuantPrevQ w, wordContinuantQ w) := by
  have h : ∀ (v : List ℕ) (m : (ℕ × ℕ) × (ℕ × ℕ)),
      (v.foldl (fun d a => ((d.1.2, (a : ℕ) * d.1.2 + d.1.1),
        (d.2.2, (a : ℕ) * d.2.2 + d.2.1))) m).2 =
      v.foldl (fun z a => (z.2, z.1 + (a : ℕ) * z.2)) m.2 := by
    intro v
    induction v with
    | nil => intro m; rfl
    | cons a v ih =>
      intro m
      simp only [List.foldl_cons]
      rw [ih]
      simp only [Nat.add_comm]
  simpa [lowerCD, wordContinuantPrevQ, wordContinuantQ, wordContinuantData]
    using (h (w.flatMap fun a => [(a : ℕ)]) ((1,0),(0,1))).symm

private theorem q_pos (w : List ℕ+) : 0 < ((lowerCD w).2 : ℝ) := by
  rw [cd_eq]
  exact_mod_cast continuant_denominator_pos w

private theorem ratio_nn (w : List ℕ+) : 0 ≤ lowerRatio w := by
  unfold lowerRatio
  positivity

private theorem tails :
    lowerAlpha ∈ Set.Icc (0 : ℝ) 1 ∧
    lowerBeta ∈ Set.Icc (0 : ℝ) 1 ∧ lowerAlpha < lowerBeta := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 21)
  have hn := Real.sqrt_nonneg (21 : ℝ)
  have hlo : 3 < Real.sqrt (21 : ℝ) := by nlinarith
  have hhi : Real.sqrt (21 : ℝ) < 5 := by nlinarith
  dsimp [lowerAlpha, lowerBeta, Set.mem_Icc]
  constructor
  · constructor <;> linarith
  constructor
  · constructor <;> linarith
  · linarith

private theorem width_pos (w : List ℕ+) : 0 < lowerWidth w := by
  unfold lowerWidth
  rw [prefixEval_difference w lowerBeta lowerAlpha tails.2.1 tails.1]
  apply div_pos
  · exact abs_pos.mpr (sub_ne_zero.mpr (ne_of_gt tails.2.2))
  · have hq : (0 : ℝ) < wordContinuantQ w := by
      exact_mod_cast continuant_denominator_pos w
    have ha := tails.1.1
    have hb := tails.2.1.1
    positivity

private noncomputable def factors (w : List ℕ+) (x y : ℝ) : ℝ :=
  (1 + lowerRatio w * x) * (1 + lowerRatio w * y)

private theorem factors_pos (w : List ℕ+) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 < factors w x y := by
  have hr := ratio_nn w
  unfold factors
  positivity

private theorem width_append (base words : List ℕ+) :
    lowerWidth (base ++ words) = lowerWidth words /
      (((lowerCD base).2 : ℝ)^2 *
        factors base (prefixEval words lowerAlpha) (prefixEval words lowerBeta)) := by
  have ha := pe_icc words lowerAlpha tails.1
  have hb := pe_icc words lowerBeta tails.2.1
  have hq := q_pos base
  have hc := cd_eq base
  unfold lowerWidth
  rw [pe_append, pe_append, prefixEval_difference base _ _ hb ha]
  congr 1
  simp only [factors, lowerRatio, hc]
  have hq' : (wordContinuantQ base : ℝ) ≠ 0 := by simpa [hc] using ne_of_gt hq
  field_simp

private theorem sort_factors (c : CertField) (x y : CertField × CertField) (r s : ℝ) :
    certThresholdVal (lowerHistoryThreshold c x y) r s =
      certFieldVal c * (1+s*certFieldVal y.1) * (1+s*certFieldVal y.2) /
        ((1+r*certFieldVal x.1) * (1+r*certFieldVal x.2)) := by
  unfold certThresholdVal certThresholdNum certThresholdDen lowerHistoryThreshold lowerHistorySort
  split_ifs <;> simp only <;> ring

private theorem field_sub (x y : CertField) :
    certFieldVal (certFieldSub x y) = certFieldVal x - certFieldVal y := by
  simp only [certFieldVal, certFieldSub]
  push_cast
  ring

private theorem field_mul (x y : CertField) :
    certFieldVal (certFieldMul x y) = certFieldVal x * certFieldVal y := by
  have h3 : Real.sqrt (3:ℝ)^2 = 3 := Real.sq_sqrt (by norm_num)
  have h7 : Real.sqrt (7:ℝ)^2 = 7 := Real.sq_sqrt (by norm_num)
  have h37 : Real.sqrt (21:ℝ) = Real.sqrt 3 * Real.sqrt 7 := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3)]
    norm_num
  simp only [certFieldVal, certFieldMul]
  push_cast
  rw [h37]
  ring_nf
  simp only [h3,h7]
  ring

private theorem field_abs
    (hsg : ∀ z : CertField,
      (lowerHistorySign z = 0 ↔ certFieldVal z = 0) ∧
      (0 < lowerHistorySign z ↔ 0 < certFieldVal z)) (z : CertField) :
    certFieldVal (lowerHistoryAbs z) = |certFieldVal z| := by
  unfold lowerHistoryAbs
  split_ifs with h
  · have hn : certFieldVal z < 0 := by
      rcases lt_trichotomy (certFieldVal z) 0 with hz | hz | hz
      · exact hz
      · have := (hsg z).1.mpr hz; omega
      · have := (hsg z).2.mpr hz; omega
    rw [abs_of_neg hn]
    simp only [lowerHistoryNeg, certFieldScale, certFieldVal]
    push_cast
    ring
  · rw [abs_of_nonneg]
    by_contra hn
    have hz : certFieldVal z < 0 := lt_of_not_ge hn
    have hsn : 0 ≤ lowerHistorySign z := le_of_not_gt h
    rcases eq_or_lt_of_le hsn with he | hp
    · have := (hsg z).1.mp he.symm; linarith
    · have := (hsg z).2.mp hp; linarith

private theorem alpha_value : certFieldVal lowerHistoryAlpha = lowerAlpha := by
  norm_num [certFieldVal, lowerHistoryAlpha, lowerAlpha]
  ring

private theorem beta_value : certFieldVal lowerHistoryBeta = lowerBeta := by
  norm_num [certFieldVal, lowerHistoryBeta, lowerBeta]
  ring

private theorem width_threshold_value (base words : LowerPair) :
    certThresholdVal (lowerHistoryWH words) (lowerRatio base.1) (lowerRatio base.2) =
      lowerScale base * (lowerWidth (base.1++words.1) / lowerWidth (base.2++words.2)) := by
  have ha (w : List ℕ+) : certFieldVal (lowerHistoryCF w lowerHistoryAlpha) =
      prefixEval w lowerAlpha := by
    rw [lowerHistory_cf_value w lowerHistoryAlpha (by rw [alpha_value]; exact tails.1.1), alpha_value]
  have hb (w : List ℕ+) : certFieldVal (lowerHistoryCF w lowerHistoryBeta) =
      prefixEval w lowerBeta := by
    rw [lowerHistory_cf_value w lowerHistoryBeta (by rw [beta_value]; exact tails.2.1.1), beta_value]
  have hy : certFieldVal (certFieldSub (lowerHistoryCF words.2 lowerHistoryAlpha)
      (lowerHistoryCF words.2 lowerHistoryBeta)) ≠ 0 := by
    rw [field_sub, ha, hb, sub_ne_zero]
    intro he
    have hw := width_pos words.2
    simp [lowerWidth, he] at hw
  have ht : certThresholdVal (lowerHistoryWH words) (lowerRatio base.1) (lowerRatio base.2) =
      (lowerWidth words.1 / lowerWidth words.2) *
        factors base.2 (prefixEval words.2 lowerAlpha) (prefixEval words.2 lowerBeta) /
        factors base.1 (prefixEval words.1 lowerAlpha) (prefixEval words.1 lowerBeta) := by
    unfold lowerHistoryWH
    rw [sort_factors, field_abs lowerHistory_sign_value]
    simp only [lowerHistoryDiv, field_mul, lowerHistory_inv_value _ hy, field_sub, ha, hb]
    rw [← div_eq_mul_inv, abs_div]
    simp only [lowerWidth, abs_sub_comm, factors]
    ring
  have hx := factors_pos base.1 _ _ (pe_icc words.1 _ tails.1).1
    (pe_icc words.1 _ tails.2.1).1
  have hyf := factors_pos base.2 _ _ (pe_icc words.2 _ tails.1).1
    (pe_icc words.2 _ tails.2.1).1
  have hqx := q_pos base.1
  have hqy := q_pos base.2
  have hwy := width_pos words.2
  rw [ht, width_append, width_append]
  unfold lowerScale
  field_simp

 private theorem scale_threshold_value (q : ℚ) (t : CertThreshold) (r s : ℝ) :
    certThresholdVal (lowerHistoryScaleThreshold q t) r s =
      (q : ℝ) * certThresholdVal t r s := by
  unfold lowerHistoryScaleThreshold certThresholdVal certThresholdNum certThresholdDen
  simp only [certFieldVal, certFieldScale]
  push_cast
  ring

 private theorem scale_pos (base : LowerPair) : 0 < lowerScale base := by
  unfold lowerScale
  exact div_pos (sq_pos_of_pos (q_pos _)) (sq_pos_of_pos (q_pos _))

 private theorem scaled_lower_cut (base words : LowerPair) :
    lowerHistoryAtBase base [⟨true,false,lowerHistoryScaleThreshold (5/7) (lowerHistoryWH words)⟩] ↔
      lowerWidth (base.1++words.1) ≤ (7/5:ℝ)*lowerWidth (base.2++words.2) := by
  simp only [lowerHistoryAtBase, lowerHistoryConditions, List.mem_singleton,
    forall_eq, certBoundHolds, Bool.false_eq_true, ↓reduceIte]
  rw [scale_threshold_value, width_threshold_value]
  norm_num only [Rat.cast_div, Rat.cast_ofNat]
  rw [show (5/7:ℝ)*(lowerScale base*(lowerWidth (base.1++words.1)/lowerWidth (base.2++words.2))) =
    lowerScale base*((5/7:ℝ)*lowerWidth (base.1++words.1)/lowerWidth (base.2++words.2)) by ring]
  conv_lhs => rhs; rw [← mul_one (lowerScale base)]
  rw [mul_le_mul_iff_right₀ (scale_pos base), div_le_iff₀ (width_pos _)]
  constructor <;> intro h <;> nlinarith only [h]

 private theorem scaled_upper_cut (base words : LowerPair) :
    lowerHistoryAtBase base [⟨false,false,lowerHistoryScaleThreshold (7/5) (lowerHistoryWH words)⟩] ↔
      lowerWidth (base.2++words.2) ≤ (7/5:ℝ)*lowerWidth (base.1++words.1) := by
  simp only [lowerHistoryAtBase, lowerHistoryConditions, List.mem_singleton,
    forall_eq, certBoundHolds, Bool.false_eq_true, ↓reduceIte]
  rw [scale_threshold_value, width_threshold_value]
  norm_num only [Rat.cast_div, Rat.cast_ofNat]
  rw [show (7/5:ℝ)*(lowerScale base*(lowerWidth (base.1++words.1)/lowerWidth (base.2++words.2))) =
    lowerScale base*((7/5:ℝ)*lowerWidth (base.1++words.1)/lowerWidth (base.2++words.2)) by ring]
  conv_lhs => lhs; rw [← mul_one (lowerScale base)]
  rw [mul_le_mul_iff_right₀ (scale_pos base), le_div_iff₀ (width_pos _)]
  simp only [one_mul]

end M7ScaledCut14


open Freiman

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 0
set_option maxRecDepth 10000

namespace Freiman


private theorem lowerHistory_pe_append (u v : List ℕ+) (x : ℝ) :
    prefixEval (u ++ v) x = prefixEval u (prefixEval v x) := by
  induction u with
  | nil => rfl
  | cons a u ih => simp only [List.cons_append, prefixEval, ih]

private theorem lowerHistory_tau_value :
    certFieldVal lowerHistoryTau = lowerTau := by
  norm_num [certFieldVal, lowerHistoryTau, lowerTau]
  ring

private theorem lowerHistory_tau_nonneg : 0 ≤ certFieldVal lowerHistoryTau := by
  rw [lowerHistory_tau_value]
  unfold lowerTau
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  nlinarith

private theorem lowerHistory_endVal_value
    (hcf : ∀ (w : List ℕ+) (z : CertField), 0 ≤ certFieldVal z →
      certFieldVal (lowerHistoryCF w z) = prefixEval w (certFieldVal z))
    (C : LowerHistoryContext) (w : LowerPair) (upper side short : Bool) :
    certFieldVal (lowerHistoryEndVal C w upper side short) =
      prefixEval (lowerHistoryPick w side ++
        (if xor (!upper) (lowerHistoryWordParity C w side) then
          if short then [2,1,3] else [3]
        else if short then [1,2,1,3] else [1,3])) lowerTau := by
  unfold lowerHistoryEndVal
  rw [hcf _ _ lowerHistory_tau_nonneg, lowerHistory_tau_value]

private theorem lowerHistory_context_suffix_3
    (base ctx words : List ℕ+) (hc : lowerHistorySuffixContext base ctx) :
    lowerEnds (base ++ words) [3] ↔ lowerEnds (ctx ++ words) [3] := by
  by_cases hw : words = []
  · subst words
    simpa using hc.2.1
  · have hw' : ∃ a ws, words = a :: ws := List.exists_cons_of_ne_nil hw
    obtain ⟨a, ws, rfl⟩ := hw'
    simp only [lowerEnds, List.singleton_suffix_iff_getLast?_eq_some]
    simp

private theorem lowerHistory_context_suffix_31
    (base ctx words : List ℕ+) (hc : lowerHistorySuffixContext base ctx) :
    lowerEnds (base ++ words) [3,1] ↔ lowerEnds (ctx ++ words) [3,1] := by
  generalize hr : words.reverse = rev
  cases rev with
  | nil =>
    have hw : words = [] := by
      have := congrArg List.reverse hr
      simpa using this
    subst words
    simpa using hc.2.2
  | cons a rev =>
    cases rev with
    | nil =>
      have hw : words = [a] := by
        have := congrArg List.reverse hr
        simpa using this
      subst words
      rw [show lowerEnds (base ++ [a]) [3,1] ↔
          a = 1 ∧ lowerEnds base [3] by
        unfold lowerEnds
        rw [← List.reverse_prefix]
        simp [← List.reverse_prefix, eq_comm],
        show lowerEnds (ctx ++ [a]) [3,1] ↔
          a = 1 ∧ lowerEnds ctx [3] by
        unfold lowerEnds
        rw [← List.reverse_prefix]
        simp [← List.reverse_prefix, eq_comm],
        hc.2.1]
    | cons b rev =>
      unfold lowerEnds
      rw [← List.reverse_prefix, ← List.reverse_prefix]
      simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, hr,
        List.append_assoc, List.nil_append]
      simp

private theorem lowerHistory_append_odd
    (base : LowerPair) (C : LowerHistoryContext)
    (hc : lowerHistoryContextFits base C) (words : LowerPair) (side : Bool) :
    decide ((lowerHistoryPick base side ++ lowerHistoryPick words side).length % 2 = 1) =
      (lowerHistoryCommonOdd base C).xor (lowerHistoryWordParity C words side) := by
  rcases base with ⟨bl, br⟩
  rcases words with ⟨wl, wr⟩
  rcases C with ⟨⟨cl, cr⟩, ⟨pl, pr⟩⟩
  cases side
  · simp only [lowerHistoryPick, lowerHistoryCommonOdd, lowerHistoryWordParity,
      Prod.fst, List.length_append]
    rcases Nat.mod_two_eq_zero_or_one bl.length with hb | hb <;>
      rcases Nat.mod_two_eq_zero_or_one wl.length with hw | hw <;>
      simp [Nat.add_mod, hb, hw]
  · have hcommon := hc.2.2
    simp only [lowerHistoryCommonOdd, lowerHistoryPick, Prod.fst, Prod.snd] at hcommon
    simp only [lowerHistoryPick, lowerHistoryCommonOdd, lowerHistoryWordParity,
      Prod.fst, Prod.snd, List.length_append]
    rw [hcommon]
    rcases Nat.mod_two_eq_zero_or_one br.length with hb | hb <;>
      rcases Nat.mod_two_eq_zero_or_one wr.length with hw | hw <;>
      simp [Nat.add_mod, hb, hw]

private theorem lowerHistory_natural_eq
    (base : LowerPair) (C : LowerHistoryContext)
    (hc : lowerHistoryContextFits base C) (words : LowerPair) (upper side : Bool) :
    lowerNaturalShort
        (lowerHistoryPick base side ++ lowerHistoryPick words side)
        (upper.xor (lowerHistoryCommonOdd base C)) =
      lowerHistoryNatural C words upper side := by
  cases side
  · have hp := lowerHistory_append_odd base C hc words false
    have hs3 := lowerHistory_context_suffix_3 base.1 C.words.1 words.1 hc.1
    have hs31 := lowerHistory_context_suffix_31 base.1 C.words.1 words.1 hc.1
    generalize hco : lowerHistoryCommonOdd base C = co at hp ⊢
    generalize hwp : lowerHistoryWordParity C words false = wp at hp ⊢
    cases upper <;> cases co <;> cases wp <;>
      simp [lowerNaturalShort, lowerHistoryNatural, hco, hwp,
        lowerHistoryPick] at hp ⊢
    all_goals
      simp [show (base.1.length + words.1.length) % 2 = _ by omega,
        hs3, hs31]
    all_goals rfl
  · have hp := lowerHistory_append_odd base C hc words true
    have hs3 := lowerHistory_context_suffix_3 base.2 C.words.2 words.2 hc.2.1
    have hs31 := lowerHistory_context_suffix_31 base.2 C.words.2 words.2 hc.2.1
    generalize hco : lowerHistoryCommonOdd base C = co at hp ⊢
    generalize hwp : lowerHistoryWordParity C words true = wp at hp ⊢
    cases upper <;> cases co <;> cases wp <;>
      simp [lowerNaturalShort, lowerHistoryNatural, hco, hwp,
        lowerHistoryPick] at hp ⊢
    all_goals
      simp [show (base.2.length + words.2.length) % 2 = _ by omega,
        hs3, hs31]
    all_goals rfl

private theorem lowerHistory_endpointSuffix_eq
    (base : LowerPair) (C : LowerHistoryContext)
    (hc : lowerHistoryContextFits base C) (words : LowerPair)
    (upper side short : Bool) :
    lowerEndpointSuffix
        (lowerHistoryPick base side ++ lowerHistoryPick words side)
        (upper.xor (lowerHistoryCommonOdd base C)) short =
      (if xor (!upper) (lowerHistoryWordParity C words side) then
        if short then [2,1,3] else [3]
      else if short then [1,2,1,3] else [1,3]) := by
  have hp := lowerHistory_append_odd base C hc words side
  generalize hco : lowerHistoryCommonOdd base C = co at hp ⊢
  generalize hwp : lowerHistoryWordParity C words side = wp at hp ⊢
  cases side <;> cases upper <;> cases short <;> cases co <;> cases wp <;>
    simp [lowerEndpointSuffix, lowerHistoryPick, hco, hwp] at hp ⊢
  all_goals
    simp [show (_ + _) % 2 = _ by omega]

private theorem lowerHistory_endVals_value
    (hcf : ∀ (w : List ℕ+) (z : CertField), 0 ≤ certFieldVal z →
      certFieldVal (lowerHistoryCF w z) = prefixEval w (certFieldVal z))
    (base : LowerPair) (C : LowerHistoryContext)
    (hc : lowerHistoryContextFits base C) (words : LowerPair)
    (upper short₀ short₁ : Bool) :
    lowerHistoryValue base C
        (lowerHistoryEndVal C words upper false short₀,
          lowerHistoryEndVal C words upper true short₁) =
      (if lowerHistoryCommonOdd base C then -1 else 1) *
        (4 +
          prefixEval ((base.1 ++ words.1) ++
            lowerEndpointSuffix (base.1 ++ words.1)
              (upper.xor (lowerHistoryCommonOdd base C)) short₀) lowerTau +
          prefixEval ((base.2 ++ words.2) ++
            lowerEndpointSuffix (base.2 ++ words.2)
              (upper.xor (lowerHistoryCommonOdd base C)) short₁) lowerTau) := by
  unfold lowerHistoryValue
  rw [lowerHistory_endVal_value hcf C words upper false short₀,
    lowerHistory_endVal_value hcf C words upper true short₁]
  have hs₀ := lowerHistory_endpointSuffix_eq base C hc words upper false short₀
  have hs₁ := lowerHistory_endpointSuffix_eq base C hc words upper true short₁
  simp only [lowerHistoryPick, Bool.false_eq_true, ↓reduceIte] at hs₀ hs₁ ⊢
  rw [hs₀, hs₁]
  simp only [lowerHistory_pe_append, List.append_assoc]

private theorem lowerHistory_physical_parity
    (base : LowerPair) (C : LowerHistoryContext)
    (hc : lowerHistoryContextFits base C) (words : LowerPair)
    (hp : lowerHistoryWordParity C words false =
      lowerHistoryWordParity C words true) :
    (base.1 ++ words.1).length % 2 = (base.2 ++ words.2).length % 2 := by
  have h₀ := lowerHistory_append_odd base C hc words false
  have h₁ := lowerHistory_append_odd base C hc words true
  rw [hp] at h₀
  have hd : decide ((base.1 ++ words.1).length % 2 = 1) =
      decide ((base.2 ++ words.2).length % 2 = 1) := h₀.trans h₁.symm
  rcases Nat.mod_two_eq_zero_or_one (base.1 ++ words.1).length with h | h <;>
    rcases Nat.mod_two_eq_zero_or_one (base.2 ++ words.2).length with k | k <;>
    simp only [List.length_append] at h k
  all_goals
    simp only [List.length_append] at hd ⊢
    simp [h, k] at hd ⊢

private theorem at_pair {base : LowerPair} {a b : CertBound}
    (ha : lowerHistoryAtBase base [a]) (hb : lowerHistoryAtBase base [b]) :
    lowerHistoryAtBase base [a,b] := by
  simpa [lowerHistoryAtBase, lowerHistoryConditions] using And.intro ha hb

private theorem normal_false (hwidth : LowerHistoryWidthLaw)
    (base words : LowerPair)
    (hw : lowerWidth (base.2 ++ words.2) ≤ lowerWidth (base.1 ++ words.1)) :
    lowerHistoryAtBase base [⟨false,false,lowerHistoryWH words⟩] :=
  (hwidth base words).1.mp hw

-- Permitted at a width tie: both orientations satisfy the non-strict tests.
private theorem normal_true_le (hwidth : LowerHistoryWidthLaw)
    (base words : LowerPair)
    (hw : lowerWidth (base.1 ++ words.1) ≤ lowerWidth (base.2 ++ words.2)) :
    lowerHistoryAtBase base [⟨true,false,lowerHistoryWH words⟩] := by
  have hn : ¬ lowerHistoryAtBase base [⟨false,true,lowerHistoryWH words⟩] := by
    rw [← (hwidth base words).2]
    exact not_lt_of_ge hw
  simp only [lowerHistoryAtBase, lowerHistoryConditions, List.mem_singleton,
    forall_eq, certBoundHolds, Bool.false_eq_true, ↓reduceIte] at hn ⊢
  exact le_of_not_gt hn

private theorem complement_lower_cut (base words : LowerPair)
    (h : ¬ lowerWidth (base.1++words.1) ≤
      (7/5:ℝ)*lowerWidth (base.2++words.2)) :
    lowerHistoryAtBase base
      [lowerHistoryComplement
        ⟨true,false,lowerHistoryScaleThreshold (5/7) (lowerHistoryWH words)⟩] := by
  have hn : ¬ lowerHistoryAtBase base
      [⟨true,false,lowerHistoryScaleThreshold (5/7) (lowerHistoryWH words)⟩] := by
    rw [M7ScaledCut14.scaled_lower_cut]
    exact h
  simp only [lowerHistoryAtBase, lowerHistoryConditions, List.mem_singleton,
    forall_eq, lowerHistoryComplement, certBoundHolds, Bool.false_eq_true,
    Bool.not_true, ↓reduceIte] at hn ⊢
  exact lt_of_not_ge hn

private theorem complement_upper_cut (base words : LowerPair)
    (h : ¬ lowerWidth (base.2++words.2) ≤
      (7/5:ℝ)*lowerWidth (base.1++words.1)) :
    lowerHistoryAtBase base
      [lowerHistoryComplement
        ⟨false,false,lowerHistoryScaleThreshold (7/5) (lowerHistoryWH words)⟩] := by
  have hn : ¬ lowerHistoryAtBase base
      [⟨false,false,lowerHistoryScaleThreshold (7/5) (lowerHistoryWH words)⟩] := by
    rw [M7ScaledCut14.scaled_upper_cut]
    exact h
  simp only [lowerHistoryAtBase, lowerHistoryConditions, List.mem_singleton,
    forall_eq, lowerHistoryComplement, certBoundHolds, Bool.false_eq_true,
    Bool.not_false, ↓reduceIte] at hn ⊢
  exact lt_of_not_ge hn

private theorem decide_of_iff {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) :
    decide p = decide q := by
  by_cases hp : p
  · have hq : q := h.mp hp
    simp [hp, hq]
  · have hq : ¬ q := mt h.mpr hp
    simp [hp, hq]

private theorem late_norm_parity (p : LowerPair) (hm : ¬ lowerMixed p) :
    (lowerNormalize p).1.length % 2 = (lowerNormalize p).2.length % 2 := by
  have hp : p.1.length % 2 = p.2.length % 2 := by
    simpa [lowerMixed] using hm
  unfold lowerNormalize
  split_ifs <;> simp [hp]

private theorem late_parity_xor (p : LowerPair) (right3 : Bool)
    (hm : lateMatches p right3) :
    (decide ((lowerNormalize p).1.length % 2 = 1)).xor (lateContext right3).parity.1 =
      (decide ((lowerNormalize p).2.length % 2 = 1)).xor (lateContext right3).parity.2 := by
  have hp := late_norm_parity p hm.1
  simp [lateContext, hp]

private theorem late_append_odd (base : LowerPair) (C : LowerHistoryContext)
    (hpar : (decide (base.1.length % 2 = 1)).xor C.parity.1 =
      (decide (base.2.length % 2 = 1)).xor C.parity.2)
    (words : LowerPair) (side : Bool) :
    decide ((lowerHistoryPick base side ++ lowerHistoryPick words side).length % 2 = 1) =
      (lowerHistoryCommonOdd base C).xor (lowerHistoryWordParity C words side) := by
  rcases base with ⟨bl, br⟩
  rcases words with ⟨wl, wr⟩
  rcases C with ⟨⟨cl, cr⟩, ⟨pl, pr⟩⟩
  cases side
  · simp only [lowerHistoryPick, lowerHistoryCommonOdd, lowerHistoryWordParity,
      Prod.fst, List.length_append]
    rcases Nat.mod_two_eq_zero_or_one bl.length with hb | hb <;>
      rcases Nat.mod_two_eq_zero_or_one wl.length with hw | hw <;>
      simp [Nat.add_mod, hb, hw]
  · simp only [lowerHistoryCommonOdd, lowerHistoryPick, Prod.fst, Prod.snd] at hpar
    simp only [lowerHistoryPick, lowerHistoryCommonOdd, lowerHistoryWordParity,
      Prod.fst, Prod.snd, List.length_append]
    rw [hpar]
    rcases Nat.mod_two_eq_zero_or_one br.length with hb | hb <;>
      rcases Nat.mod_two_eq_zero_or_one wr.length with hw | hw <;>
      simp [Nat.add_mod, hb, hw]

private theorem late_ends3_append (base w : List ℕ+) (hw : w ≠ []) :
    lowerEnds (base ++ w) [3] ↔ lowerEnds w [3] := by
  simp only [lowerEnds, List.singleton_suffix_iff_getLast?_eq_some]
  cases w with
  | nil => exact (hw rfl).elim
  | cons a t => simp [List.getLast?_append]

private theorem suffix_31_not_3 {w : List ℕ+}
    (h : ([3,1] : List ℕ+).IsSuffix w) : ¬ ([3] : List ℕ+).IsSuffix w := by
  intro h3
  obtain ⟨t, rfl⟩ := h
  have h1 : (t ++ [3,1]).getLast? = some (1 : ℕ+) := by
    simp [List.getLast?_append]
  have h3' : (t ++ [3,1]).getLast? = some (3 : ℕ+) :=
    (List.singleton_suffix_iff_getLast?_eq_some).mp h3
  simp [h1] at h3'

private theorem late_side_ends3 (p : LowerPair) (right3 side : Bool)
    (hm : lateMatches p right3) :
    lowerEnds (lowerHistoryPick (lowerNormalize p) side) [3] ↔
      lowerEnds (lowerHistoryPick (lateContext right3).words side) [3] := by
  cases side
  · have n3 : ¬ ([3] : List ℕ+).IsSuffix (lowerNormalize p).1 :=
      suffix_31_not_3 hm.2.1
    have n3c : ¬ ([3] : List ℕ+).IsSuffix [3,1] := by decide
    simp [lowerHistoryPick, lateContext, lowerEnds, n3, n3c]
  · simp [lowerHistoryPick, lateContext, lowerEnds]
    cases right3
    · have : ¬ ([3] : List ℕ+).IsSuffix (lowerNormalize p).2 := by
        simpa [lowerEnds] using hm.2.2
      have n3c : ¬ ([3] : List ℕ+).IsSuffix [3,1] := by decide
      simp [this, n3c]
    · have : ([3] : List ℕ+).IsSuffix (lowerNormalize p).2 := by
        simpa [lowerEnds] using hm.2.2
      simp [this]

private theorem late_ends31_append (base ctx w : List ℕ+) (hw : w ≠ [])
    (h3 : lowerEnds base [3] ↔ lowerEnds ctx [3]) :
    lowerEnds (base ++ w) [3,1] ↔ lowerEnds (ctx ++ w) [3,1] := by
  generalize hr : w.reverse = rev
  cases rev with
  | nil =>
    have : w = [] := by
      have := congrArg List.reverse hr
      simpa using this
    exact (hw this).elim
  | cons a rev =>
    cases rev with
    | nil =>
      have hw1 : w = [a] := by
        have := congrArg List.reverse hr
        simpa using this
      subst w
      rw [show lowerEnds (base ++ [a]) [3,1] ↔
          a = 1 ∧ lowerEnds base [3] by
        unfold lowerEnds
        rw [← List.reverse_prefix]
        simp [← List.reverse_prefix, eq_comm],
        show lowerEnds (ctx ++ [a]) [3,1] ↔
          a = 1 ∧ lowerEnds ctx [3] by
        unfold lowerEnds
        rw [← List.reverse_prefix]
        simp [← List.reverse_prefix, eq_comm],
        h3]
    | cons b rev =>
      unfold lowerEnds
      rw [← List.reverse_prefix, ← List.reverse_prefix]
      simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, hr,
        List.append_assoc, List.nil_append]
      simp

private theorem late_natural_eq (p : LowerPair) (right3 : Bool)
    (hm : lateMatches p right3) (words : LowerPair)
    (hne : ∀ side : Bool, lowerHistoryPick words side ≠ [])
    (upper side : Bool) :
    lowerNaturalShort
        (lowerHistoryPick (lowerNormalize p) side ++ lowerHistoryPick words side)
        (upper.xor (lowerHistoryCommonOdd (lowerNormalize p) (lateContext right3))) =
      lowerHistoryNatural (lateContext right3) words upper side := by
  set base := lowerNormalize p
  set C := lateContext right3
  have hpar := late_parity_xor p right3 hm
  cases side
  · have hp := late_append_odd base C hpar words false
    have hs3 := late_ends3_append base.1 words.1
      (by simpa [lowerHistoryPick] using hne false)
    have hs3c := late_ends3_append C.words.1 words.1
      (by simpa [lowerHistoryPick] using hne false)
    have h3iff := late_side_ends3 p right3 false hm
    have hs31 := late_ends31_append base.1 C.words.1 words.1
      (by simpa [lowerHistoryPick] using hne false)
      (by simpa [lowerHistoryPick] using h3iff)
    generalize hco : lowerHistoryCommonOdd base C = co at hp ⊢
    generalize hwp : lowerHistoryWordParity C words false = wp at hp ⊢
    cases upper <;> cases co <;> cases wp <;>
      simp [lowerNaturalShort, lowerHistoryNatural, hco, hwp,
        lowerHistoryPick] at hp ⊢
    all_goals
      simp [show (base.1.length + words.1.length) % 2 = _ by omega, hs3, hs3c, hs31]
    all_goals try rfl
    all_goals try exact decide_of_iff hs31
    all_goals try exact decide_of_iff (hs3.trans hs3c.symm)
    all_goals try (simpa [lowerEnds] using hs3c.symm)
    all_goals (try simp [lowerEnds]; try rfl)
  · have hp := late_append_odd base C hpar words true
    have hs3 := late_ends3_append base.2 words.2
      (by simpa [lowerHistoryPick] using hne true)
    have hs3c := late_ends3_append C.words.2 words.2
      (by simpa [lowerHistoryPick] using hne true)
    have h3iff := late_side_ends3 p right3 true hm
    have hs31 := late_ends31_append base.2 C.words.2 words.2
      (by simpa [lowerHistoryPick] using hne true)
      (by simpa [lowerHistoryPick] using h3iff)
    generalize hco : lowerHistoryCommonOdd base C = co at hp ⊢
    generalize hwp : lowerHistoryWordParity C words true = wp at hp ⊢
    cases upper <;> cases co <;> cases wp <;>
      simp [lowerNaturalShort, lowerHistoryNatural, hco, hwp,
        lowerHistoryPick] at hp ⊢
    all_goals
      simp [show (base.2.length + words.2.length) % 2 = _ by omega, hs3, hs3c, hs31]
    all_goals try rfl
    all_goals try exact decide_of_iff hs31
    all_goals try exact decide_of_iff (hs3.trans hs3c.symm)
    all_goals try (simpa [lowerEnds] using hs3c.symm)
    all_goals (try simp [lowerEnds]; try rfl)

private theorem late_endpointSuffix_eq (p : LowerPair) (right3 : Bool)
    (hm : lateMatches p right3) (words : LowerPair)
    (hne : ∀ side : Bool, lowerHistoryPick words side ≠ [])
    (upper side short : Bool) :
    lowerEndpointSuffix
        (lowerHistoryPick (lowerNormalize p) side ++ lowerHistoryPick words side)
        (upper.xor (lowerHistoryCommonOdd (lowerNormalize p) (lateContext right3)))
        short =
      (if xor (!upper) (lowerHistoryWordParity (lateContext right3) words side) then
        if short then [2,1,3] else [3]
      else if short then [1,2,1,3] else [1,3]) := by
  set base := lowerNormalize p
  set C := lateContext right3
  have hpar := late_parity_xor p right3 hm
  have hp := late_append_odd base C hpar words side
  generalize hco : lowerHistoryCommonOdd base C = co at hp ⊢
  generalize hwp : lowerHistoryWordParity C words side = wp at hp ⊢
  cases side <;> cases upper <;> cases short <;> cases co <;> cases wp <;>
    simp [lowerEndpointSuffix, lowerHistoryPick, hco, hwp] at hp ⊢
  all_goals
    simp [show (_ + _) % 2 = _ by omega]

private theorem late_endVals_value
    (hcf : ∀ (w : List ℕ+) (z : CertField), 0 ≤ certFieldVal z →
      certFieldVal (lowerHistoryCF w z) = prefixEval w (certFieldVal z))
    (p : LowerPair) (right3 : Bool) (hm : lateMatches p right3)
    (words : LowerPair) (hne : ∀ side : Bool, lowerHistoryPick words side ≠ [])
    (upper short₀ short₁ : Bool) :
    lowerHistoryValue (lowerNormalize p) (lateContext right3)
        (lowerHistoryEndVal (lateContext right3) words upper false short₀,
          lowerHistoryEndVal (lateContext right3) words upper true short₁) =
      (if lowerHistoryCommonOdd (lowerNormalize p) (lateContext right3) then -1 else 1) *
        (4 +
          prefixEval ((lowerNormalize p).1 ++ words.1 ++
            lowerEndpointSuffix ((lowerNormalize p).1 ++ words.1)
              (upper.xor (lowerHistoryCommonOdd (lowerNormalize p) (lateContext right3)))
              short₀) lowerTau +
          prefixEval ((lowerNormalize p).2 ++ words.2 ++
            lowerEndpointSuffix ((lowerNormalize p).2 ++ words.2)
              (upper.xor (lowerHistoryCommonOdd (lowerNormalize p) (lateContext right3)))
              short₁) lowerTau) := by
  set base := lowerNormalize p
  set C := lateContext right3
  unfold lowerHistoryValue
  rw [lowerHistory_endVal_value hcf C words upper false short₀,
    lowerHistory_endVal_value hcf C words upper true short₁]
  have hs₀ := late_endpointSuffix_eq p right3 hm words hne upper false short₀
  have hs₁ := late_endpointSuffix_eq p right3 hm words hne upper true short₁
  simp only [lowerHistoryPick, Bool.false_eq_true, ↓reduceIte] at hs₀ hs₁ ⊢
  rw [hs₀, hs₁]
  simp [base, C, lowerHistory_pe_append, List.append_assoc]

private theorem late_physical_parity (p : LowerPair) (right3 : Bool)
    (hm : lateMatches p right3) (words : LowerPair)
    (hp : lowerHistoryWordParity (lateContext right3) words false =
      lowerHistoryWordParity (lateContext right3) words true) :
    ((lowerNormalize p).1 ++ words.1).length % 2 =
      ((lowerNormalize p).2 ++ words.2).length % 2 := by
  set base := lowerNormalize p
  set C := lateContext right3
  have hpar := late_parity_xor p right3 hm
  have h₀ := late_append_odd base C hpar words false
  have h₁ := late_append_odd base C hpar words true
  rw [hp] at h₀
  have hd : decide ((base.1 ++ words.1).length % 2 = 1) =
      decide ((base.2 ++ words.2).length % 2 = 1) := h₀.trans h₁.symm
  rcases Nat.mod_two_eq_zero_or_one (base.1 ++ words.1).length with h | h <;>
    rcases Nat.mod_two_eq_zero_or_one (base.2 ++ words.2).length with k | k
  all_goals
    simp only [List.length_append] at h k hd ⊢
    simp [h, k] at hd ⊢

private theorem equalWords_pos (q : LowerPair) (u : Bool)
    (hw : lowerWidth q.2 ≤ lowerWidth q.1)
    {s1 s2 : Bool}
    (h1 : lowerNaturalShort q.1 u = s1)
    (h2 : lowerNaturalShort q.2 u = s2) :
    lowerEqualWords q u =
      let e : List ℕ+ := if (q.1.length % 2 = 0) = (!u) then [3] else [1,3]
      let shorten := !s1 && !s2 &&
        decide (lowerWidth (q.1 ++ e) ≤ (7 / 5 : ℝ) * lowerWidth (q.2 ++ e))
      (q.1 ++ lowerEndpointSuffix q.1 u s1,
       q.2 ++ lowerEndpointSuffix q.2 u (s2 || shorten)) := by
  unfold lowerEqualWords
  have hN : lowerNormalize q = q := by
    unfold lowerNormalize
    simp [hw]
  simp [hN, hw, h1, h2]

private theorem equalWords_neg (q : LowerPair) (u : Bool)
    (hw : ¬ lowerWidth q.2 ≤ lowerWidth q.1)
    {s1 s2 : Bool}
    (h1 : lowerNaturalShort q.1 u = s1)
    (h2 : lowerNaturalShort q.2 u = s2) :
    lowerEqualWords q u =
      let e : List ℕ+ := if (q.2.length % 2 = 0) = (!u) then [3] else [1,3]
      let shorten := !s2 && !s1 &&
        decide (lowerWidth (q.2 ++ e) ≤ (7 / 5 : ℝ) * lowerWidth (q.1 ++ e))
      (q.1 ++ lowerEndpointSuffix q.1 u (s1 || shorten),
       q.2 ++ lowerEndpointSuffix q.2 u s2) := by
  unfold lowerEqualWords
  have hN : lowerNormalize q = (q.2, q.1) := by
    unfold lowerNormalize
    simp [hw]
  simp [hN, hw, h1, h2]

private theorem late_endpoint_from_words
    (hcf : ∀ (w : List ℕ+) (z : CertField), 0 ≤ certFieldVal z →
      certFieldVal (lowerHistoryCF w z) = prefixEval w (certFieldVal z))
    (p : LowerPair) (right3 : Bool) (hm : lateMatches p right3)
    (words : LowerPair) (hne : ∀ side : Bool, lowerHistoryPick words side ≠ [])
    (upper short₀ short₁ : Bool)
    (hw :
      lowerEndpointWords (lowerHistoryAppend (lowerNormalize p) words)
          (upper.xor (lowerHistoryCommonOdd (lowerNormalize p) (lateContext right3))) =
        ((lowerNormalize p).1 ++ words.1 ++
            lowerEndpointSuffix ((lowerNormalize p).1 ++ words.1)
              (upper.xor (lowerHistoryCommonOdd (lowerNormalize p) (lateContext right3)))
              short₀,
          (lowerNormalize p).2 ++ words.2 ++
            lowerEndpointSuffix ((lowerNormalize p).2 ++ words.2)
              (upper.xor (lowerHistoryCommonOdd (lowerNormalize p) (lateContext right3)))
              short₁)) :
    lowerHistoryEndpointReal (lowerNormalize p) (lateContext right3) words upper =
      lowerHistoryValue (lowerNormalize p) (lateContext right3)
        (lowerHistoryEndVal (lateContext right3) words upper false short₀,
          lowerHistoryEndVal (lateContext right3) words upper true short₁) := by
  rw [late_endVals_value hcf p right3 hm words hne upper short₀ short₁]
  unfold lowerHistoryEndpointReal lowerHistoryAppend
  change (if lowerHistoryCommonOdd (lowerNormalize p) (lateContext right3) then -1 else 1) *
      (4 + prefixEval
        (lowerEndpointWords ((lowerNormalize p).1 ++ words.1, (lowerNormalize p).2 ++ words.2)
          (upper.xor (lowerHistoryCommonOdd (lowerNormalize p) (lateContext right3)))).1 lowerTau +
        prefixEval
        (lowerEndpointWords ((lowerNormalize p).1 ++ words.1, (lowerNormalize p).2 ++ words.2)
          (upper.xor (lowerHistoryCommonOdd (lowerNormalize p) (lateContext right3)))).2 lowerTau) = _
  have hw' :
      lowerEndpointWords ((lowerNormalize p).1 ++ words.1, (lowerNormalize p).2 ++ words.2)
        (upper.xor (lowerHistoryCommonOdd (lowerNormalize p) (lateContext right3))) =
      ((lowerNormalize p).1 ++ words.1 ++
          lowerEndpointSuffix ((lowerNormalize p).1 ++ words.1)
            (upper.xor (lowerHistoryCommonOdd (lowerNormalize p) (lateContext right3))) short₀,
        (lowerNormalize p).2 ++ words.2 ++
          lowerEndpointSuffix ((lowerNormalize p).2 ++ words.2)
            (upper.xor (lowerHistoryCommonOdd (lowerNormalize p) (lateContext right3))) short₁) := by
    simpa only [lowerHistoryAppend] using hw
  rw [hw']

private theorem normal_true_strict (hwidth : LowerHistoryWidthLaw)
    (base words : LowerPair)
    (hw : ¬ lowerWidth (base.2 ++ words.2) ≤ lowerWidth (base.1 ++ words.1)) :
    lowerHistoryAtBase base [⟨true,true,lowerHistoryWH words⟩] := by
  have hn : ¬ lowerHistoryAtBase base [⟨false,false,lowerHistoryWH words⟩] := by
    rw [← (hwidth base words).1]
    exact hw
  simp only [lowerHistoryAtBase, lowerHistoryConditions, List.mem_singleton,
    forall_eq, certBoundHolds, Bool.false_eq_true, ↓reduceIte] at hn ⊢
  exact lt_of_not_ge hn

private theorem late_holds_atBase (p : LowerPair) (cs : List CertBound) :
    lateHolds cs (lateR p) (lateS p) (lateQ p) ↔
      lowerHistoryAtBase (lowerNormalize p) cs := by
  simp [lateHolds, lateR, lateS, lateQ, lowerHistoryAtBase, lowerHistoryConditions]

private theorem late_actual_endpoint (p : LowerPair) (right3 : Bool)
    (words : LowerPair) (upper : Bool) :
    lateActualEndpoint p words upper =
      lowerHistoryEndpointReal (lowerNormalize p) (lateContext right3) words upper := by
  unfold lateActualEndpoint lowerHistoryEndpointReal lowerHistoryCommonOdd lateContext
  cases right3 <;> simp

private theorem late_actual_value (p : LowerPair) (right3 : Bool)
    (z : CertField × CertField) :
    lateActualValue p z =
      lowerHistoryValue (lowerNormalize p) (lateContext right3) z := by
  unfold lateActualValue lowerHistoryValue lowerHistoryCommonOdd lateContext
  cases right3 <;> simp

private theorem late_equal_core
    (hwidth : LowerHistoryWidthLaw)
    (hcf : ∀ (w : List ℕ+) (z : CertField), 0 ≤ certFieldVal z →
      certFieldVal (lowerHistoryCF w z) = prefixEval w (certFieldVal z))
    (p : LowerPair) (e : LateEndpoint)
    (hm : lateMatches p e.right3)
    (hne : ∀ side : Bool, lowerHistoryPick e.words side ≠ [])
    (hp : lowerHistoryWordParity (lateContext e.right3) e.words false =
      lowerHistoryWordParity (lateContext e.right3) e.words true) :
    ∃ z cs, (z,cs) ∈ lateEndpointCases e.right3 e.words e.upper ∧
      lowerHistoryAtBase (lowerNormalize p) cs ∧
      lowerHistoryEndpointReal (lowerNormalize p) (lateContext e.right3)
        e.words e.upper =
        lowerHistoryValue (lowerNormalize p) (lateContext e.right3) z := by
  set base := lowerNormalize p
  set C := lateContext e.right3
  set words := e.words
  set upper := e.upper
  have hpar := late_physical_parity p e.right3 hm words hp
  have hs₀ := late_natural_eq p e.right3 hm words hne upper false
  have hs₁ := late_natural_eq p e.right3 hm words hne upper true
  generalize hn₀ : lowerHistoryNatural C words upper false = b₀ at hs₀
  generalize hn₁ : lowerHistoryNatural C words upper true = b₁ at hs₁
  cases b₀ <;> cases b₁
  · let ext : List ℕ+ :=
      if xor (!upper) (lowerHistoryWordParity C words false) then [3] else [1,3]
    let aux : LowerPair := (words.1 ++ ext, words.2 ++ ext)
    by_cases hw : lowerWidth (base.2 ++ words.2) ≤ lowerWidth (base.1 ++ words.1)
    · let sh : Bool := decide
        (lowerWidth (base.1 ++ aux.1) ≤ (7/5:ℝ) * lowerWidth (base.2 ++ aux.2))
      let norm : CertBound := ⟨false,false,lowerHistoryWH words⟩
      let cut : CertBound :=
        ⟨true,false,lowerHistoryScaleThreshold (5/7) (lowerHistoryWH aux)⟩
      refine ⟨(lowerHistoryEndVal C words upper false false,
          lowerHistoryEndVal C words upper true sh),
        [norm, if sh then cut else lowerHistoryComplement cut], ?_, ?_, ?_⟩
      · unfold lateEndpointCases
        rw [if_pos hp]
        dsimp only [lateEqualCases]
        rw [if_neg (by simp [hn₀, hn₁, C])]
        simp only [List.mem_flatMap]
        refine ⟨(false, ⟨false, false, lowerHistoryWH words⟩), by simp [lateNormals], ?_⟩
        simp only [List.mem_map]
        refine ⟨sh, by cases sh <;> simp, ?_⟩
        have hext : (xor (!upper) (lowerHistoryWordParity C words false) = true) ↔
            (upper = lowerHistoryWordParity C words false) := by
          cases upper <;> cases (lowerHistoryWordParity C words false) <;> simp
        cases sh <;> simp [norm, cut, aux, ext, C, hext]
      · apply at_pair
        · exact normal_false hwidth base words hw
        · by_cases hh : lowerWidth (base.1 ++ aux.1) ≤
              (7/5:ℝ) * lowerWidth (base.2 ++ aux.2)
          · simp [sh, hh, cut]
            exact M7ScaledCut14.scaled_lower_cut base aux |>.mpr hh
          · simp [sh, hh, cut]
            exact complement_lower_cut base aux hh
      · apply late_endpoint_from_words hcf p e.right3 hm words hne upper false sh
        simp only [lowerHistoryAppend]
        unfold lowerEndpointWords
        rw [if_pos hpar]
        have hs0p : lowerNaturalShort (base.1 ++ words.1)
            (upper.xor (lowerHistoryCommonOdd base C)) = false := by
          simpa only [lowerHistoryPick, Bool.false_eq_true, ↓reduceIte] using hs₀
        have hs1p : lowerNaturalShort (base.2 ++ words.2)
            (upper.xor (lowerHistoryCommonOdd base C)) = false := by
          simpa only [lowerHistoryPick, ↓reduceIte] using hs₁
        have he0 := late_endpointSuffix_eq p e.right3 hm words hne upper false false
        have he0' : (if ((base.1 ++ words.1).length % 2 = 0) =
            !(upper.xor (lowerHistoryCommonOdd base C)) then ([3] : List ℕ+) else [1,3]) =
            ext := by
          simpa [lowerEndpointSuffix, lowerHistoryPick, ext] using he0
        rw [equalWords_pos _ _ hw hs0p hs1p]
        have hshort : decide
            (lowerWidth ((base.1 ++ words.1) ++ ext) ≤
              (7 / 5 : ℝ) * lowerWidth ((base.2 ++ words.2) ++ ext)) = sh := by
          simp [sh, aux, List.append_assoc]
        simp only [hs0p, hs1p, Bool.not_false, Bool.true_and, Bool.false_or]
        rw [he0']
        simp [List.append_assoc]
        try (congr 1; simpa [base, List.append_assoc] using hshort)
        try rfl
    · let sh : Bool := decide
        (lowerWidth (base.2 ++ aux.2) ≤ (7/5:ℝ) * lowerWidth (base.1 ++ aux.1))
      let norm : CertBound := ⟨true,true,lowerHistoryWH words⟩
      let cut : CertBound :=
        ⟨false,false,lowerHistoryScaleThreshold (7/5) (lowerHistoryWH aux)⟩
      refine ⟨(lowerHistoryEndVal C words upper false sh,
          lowerHistoryEndVal C words upper true false),
        [norm, if sh then cut else lowerHistoryComplement cut], ?_, ?_, ?_⟩
      · unfold lateEndpointCases
        rw [if_pos hp]
        dsimp only [lateEqualCases]
        rw [if_neg (by simp [hn₀, hn₁, C])]
        simp only [List.mem_flatMap]
        refine ⟨(true, ⟨true, true, lowerHistoryWH words⟩), by simp [lateNormals], ?_⟩
        simp only [List.mem_map]
        refine ⟨sh, by cases sh <;> simp, ?_⟩
        have hext : (xor (!upper) (lowerHistoryWordParity C words false) = true) ↔
            (upper = lowerHistoryWordParity C words false) := by
          cases upper <;> cases (lowerHistoryWordParity C words false) <;> simp
        cases sh <;> simp [norm, cut, aux, ext, C, hext]
      · apply at_pair
        · exact normal_true_strict hwidth base words hw
        · by_cases hh : lowerWidth (base.2 ++ aux.2) ≤
              (7/5:ℝ) * lowerWidth (base.1 ++ aux.1)
          · simp [sh, hh, cut]
            exact M7ScaledCut14.scaled_upper_cut base aux |>.mpr hh
          · simp [sh, hh, cut]
            exact complement_upper_cut base aux hh
      · apply late_endpoint_from_words hcf p e.right3 hm words hne upper sh false
        simp only [lowerHistoryAppend]
        unfold lowerEndpointWords
        rw [if_pos hpar]
        have hs0p : lowerNaturalShort (base.1 ++ words.1)
            (upper.xor (lowerHistoryCommonOdd base C)) = false := by
          simpa only [lowerHistoryPick, Bool.false_eq_true, ↓reduceIte] using hs₀
        have hs1p : lowerNaturalShort (base.2 ++ words.2)
            (upper.xor (lowerHistoryCommonOdd base C)) = false := by
          simpa only [lowerHistoryPick, ↓reduceIte] using hs₁
        have he1 := late_endpointSuffix_eq p e.right3 hm words hne upper true false
        have he1' : (if ((base.2 ++ words.2).length % 2 = 0) =
            !(upper.xor (lowerHistoryCommonOdd base C)) then ([3] : List ℕ+) else [1,3]) =
            ext := by
          simpa [lowerEndpointSuffix, lowerHistoryPick, ext, hp] using he1
        rw [equalWords_neg _ _ hw hs0p hs1p]
        have hshort : decide
            (lowerWidth ((base.2 ++ words.2) ++ ext) ≤
              (7 / 5 : ℝ) * lowerWidth ((base.1 ++ words.1) ++ ext)) = sh := by
          simp [sh, aux, List.append_assoc]
        simp only [hs0p, hs1p, Bool.not_false, Bool.true_and, Bool.false_or]
        rw [he1']
        simp [List.append_assoc]
        try (congr 1; simpa [base, List.append_assoc] using hshort)
        try rfl
  all_goals
    refine ⟨(lowerHistoryEndVal C words upper false
          (lowerHistoryNatural C words upper false),
        lowerHistoryEndVal C words upper true
          (lowerHistoryNatural C words upper true)), [], ?_, by simp
          [lowerHistoryAtBase, lowerHistoryConditions], ?_⟩
    · unfold lateEndpointCases
      rw [if_pos hp]
      simp [lateEqualCases, hn₀, hn₁, C]
    · apply late_endpoint_from_words hcf p e.right3 hm words hne upper
          (lowerHistoryNatural C words upper false)
          (lowerHistoryNatural C words upper true)
      simp only [lowerHistoryAppend]
      unfold lowerEndpointWords
      rw [if_pos hpar]
      have hs0p := hs₀
      have hs1p := hs₁
      simp only [lowerHistoryPick, Bool.false_eq_true, ↓reduceIte] at hs0p
      simp only [lowerHistoryPick, ↓reduceIte] at hs1p
      by_cases hw : lowerWidth (base.2 ++ words.2) ≤ lowerWidth (base.1 ++ words.1)
      · rw [equalWords_pos _ _ hw hs0p hs1p]
        simp [hs0p, hs1p, hn₀, hn₁, List.append_assoc]
      · rw [equalWords_neg _ _ hw hs0p hs1p]
        simp [hs0p, hs1p, hn₀, hn₁, List.append_assoc]

private theorem late_finset_holds (base : LowerPair) (cs bs : List CertBound)
    (h : cs.toFinset = bs.toFinset)
    (hh : lateHolds bs (lowerRatio base.1) (lowerRatio base.2) (lowerScale base)) :
    lowerHistoryAtBase base cs := by
  intro b hb
  have hbF : b ∈ cs.toFinset := (List.mem_toFinset (l := cs)).mpr hb
  rw [h] at hbF
  exact hh b ((List.mem_toFinset (l := bs)).mp hbF)

private theorem at_head {base : LowerPair} {a b : CertBound}
    (h : lowerHistoryAtBase base [a, b]) : lowerHistoryAtBase base [a] := by
  intro c hc
  simp at hc
  subst c
  exact h a (by simp)

private theorem at_mem {base : LowerPair} {cs : List CertBound} {a : CertBound}
    (h : lowerHistoryAtBase base cs) (ha : a ∈ cs) :
    lowerHistoryAtBase base [a] := fun b hb => by
  simp at hb
  subst b
  exact h a ha

private theorem at_tail {base : LowerPair} {a b : CertBound}
    (h : lowerHistoryAtBase base [a, b]) : lowerHistoryAtBase base [b] := by
  intro c hc
  simp at hc
  subst c
  exact h b (by simp)

private theorem not_cut_and_complement (base : LowerPair) (c : CertBound) :
    ¬ (lowerHistoryAtBase base [c] ∧
       lowerHistoryAtBase base [lowerHistoryComplement c]) := by
  intro ⟨ha, hb⟩
  simp only [lowerHistoryAtBase, lowerHistoryConditions, List.mem_singleton,
    forall_eq, lowerHistoryComplement, certBoundHolds] at ha hb
  cases hL : c.lower <;> cases hS : c.strict <;>
    simp [hL, hS, Bool.not_true, Bool.not_false] at ha hb <;> linarith

private theorem not_both_late_normals (base words : LowerPair) :
    ¬ (lowerHistoryAtBase base [⟨false, false, lowerHistoryWH words⟩] ∧
       lowerHistoryAtBase base [⟨true, true, lowerHistoryWH words⟩]) := by
  intro ⟨hL, hR⟩
  simp only [lowerHistoryAtBase, lowerHistoryConditions, List.mem_singleton,
    forall_eq, certBoundHolds, Bool.false_eq_true, ↓reduceIte] at hL hR
  exact (not_le_of_gt hR hL).elim

private theorem late_normals_decode (w : LowerPair) {wide : Bool} {norm : CertBound}
    (h : (wide, norm) ∈ lateNormals w) :
    (wide = false ∧ norm = ⟨false, false, lowerHistoryWH w⟩) ∨
    (wide = true ∧ norm = ⟨true, true, lowerHistoryWH w⟩) := by
  simpa [lateNormals] using h

private theorem late_equal_holding_unique
    (base : LowerPair) (C : LowerHistoryContext) (words : LowerPair) (upper : Bool)
    {z z' : CertField × CertField} {cs cs' : List CertBound}
    (h : (z, cs) ∈ lateEqualCases C words upper)
    (h' : (z', cs') ∈ lateEqualCases C words upper)
    (hat : lowerHistoryAtBase base cs)
    (hat' : lowerHistoryAtBase base cs') :
    z = z' := by
  by_cases hn : lowerHistoryNatural C words upper false = true ∨
      lowerHistoryNatural C words upper true = true
  · simp [lateEqualCases, hn] at h h'
    exact h.1.trans h'.1.symm
  · simp [lateEqualCases, hn, lateNormals] at h h'
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        ((try rfl) <;>
          (try exact (not_cut_and_complement base _
            ⟨at_tail hat, at_tail hat'⟩).elim) <;>
          (try exact (not_cut_and_complement base _
            ⟨at_tail hat', at_tail hat⟩).elim) <;>
          (try exact (not_both_late_normals base words
            ⟨at_mem hat List.mem_cons_self,
              at_mem hat' List.mem_cons_self⟩).elim) <;>
          (try exact (not_both_late_normals base words
            ⟨at_mem hat' List.mem_cons_self,
              at_mem hat List.mem_cons_self⟩).elim))

end Freiman

open Freiman

theorem solution
    (hcf : ∀ (w : List ℕ+) (z : CertField), 0 ≤ certFieldVal z →
      certFieldVal (lowerHistoryCF w z) = prefixEval w (certFieldVal z))
    (hw : LowerHistoryWidthLaw)
    (p : LowerPair) (e : LateEndpoint)
    (hm : lateMatches p e.right3)
    (hne1 : e.words.1 ≠ []) (hne2 : e.words.2 ≠ [])
    (hv : lateEndpointValid lateCatalog e)
    (hp : lowerHistoryWordParity (lateContext e.right3) e.words false =
      lowerHistoryWordParity (lateContext e.right3) e.words true) :
    ∀ ids ∈ e.modes,
      lateHolds (lateBounds lateCatalog ids) (lateR p) (lateS p) (lateQ p) →
      lateActualEndpoint p e.words e.upper = lateActualValue p e.value := by
  intro ids hids hholds
  have hne : ∀ side : Bool, lowerHistoryPick e.words side ≠ [] := by
    intro side; cases side <;> simpa [lowerHistoryPick] using ‹_›
  obtain ⟨z, cs, hmem, hat, hval⟩ :=
    late_equal_core hw hcf p e hm hne hp
  obtain ⟨_, _, _, hmode⟩ := hv
  obtain ⟨_, ⟨cs', hmem', hfin⟩⟩ := hmode ids hids
  have hholds' : lateHolds cs' (lateR p) (lateS p) (lateQ p) := by
    intro b hb
    have hbF : b ∈ cs'.toFinset := (List.mem_toFinset (l := cs')).mpr hb
    rw [hfin] at hbF
    exact hholds b ((List.mem_toFinset (l := lateBounds lateCatalog ids)).mp hbF)
  have hat' : lowerHistoryAtBase (lowerNormalize p) cs' :=
    (late_holds_atBase p cs').mp hholds'
  have hmemE : (e.value, cs') ∈ lateEqualCases (lateContext e.right3) e.words e.upper := by
    unfold lateEndpointCases at hmem'
    rwa [if_pos hp] at hmem'
  have hmemZ : (z, cs) ∈ lateEqualCases (lateContext e.right3) e.words e.upper := by
    unfold lateEndpointCases at hmem
    rwa [if_pos hp] at hmem
  have hz : z = e.value :=
    late_equal_holding_unique (lowerNormalize p) (lateContext e.right3)
      e.words e.upper hmemZ hmemE hat hat'
  rw [late_actual_endpoint p e.right3, late_actual_value p e.right3, ← hz]
  exact hval
