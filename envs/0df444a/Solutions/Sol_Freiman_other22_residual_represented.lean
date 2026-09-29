-- Prove2me | solution 1 for Freiman.other22_residual_represented
-- status  : ACCEPTED   (prove)
-- author  : @Koki Yamada
-- created : 2026-09-15T23:14:15.628245+00:00
-- url     : https://prove2.me/submissions/9ea1b5cf-e0a4-49bc-9d90-776e8325523a

import Definitions.Def_Freiman_other22Verification
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

private theorem residual_child (Z B R S : LowerPair)
    (h : LowerOther22Geometry Z B R S) :
    lowerChild S ([2],[1]) =
      (Z.2 ++ [3,1,2], Z.1 ++ [2,2,1]) := by
  have hB : B = (Z.1 ++ [2], Z.2 ++ [3]) := by
    rw [h.birth]
    simp [lowerChild, h.normalizedZ]
  have hS : S = (Z.2 ++ [3,1], Z.1 ++ [2,2]) := by
    rw [h.stepS]
    simp [lowerChild, h.normalizedR, hB, List.append_assoc]
  unfold lowerChild
  simp only [h.normalizedS]
  simp [hS]

private theorem residual_endpointWords_eq (Q : LowerPair) (u : Bool)
    (hpar : Q.1.length % 2 = Q.2.length % 2) :
    lowerEndpointWords Q u = lowerEqualWords Q u := by
  unfold lowerEndpointWords
  rw [if_pos hpar]

private theorem residual_ext_eq (Z : LowerPair) (k : Fin 6)
    (hc : lowerHistoryContextFits Z (other22Context k))
    (hp : lowerHistoryWordParity (other22Context k) other22ResidualWords false =
      lowerHistoryWordParity (other22Context k) other22ResidualWords true) :
    (if (Z.2.length + 3) % 2 = 0 ↔
        lowerHistoryCommonOdd Z (other22Context k) = false then ([3] : List ℕ+) else [1,3]) =
      (if lowerHistoryWordParity (other22Context k) other22ResidualWords false = false
        then ([3] : List ℕ+) else [1,3]) := by
  rw [hp]
  have h := lowerHistory_endpointSuffix_eq Z (other22Context k) hc
    other22ResidualWords false true false
  simp [other22ResidualWords, lowerEndpointSuffix, lowerHistoryPick,
    Bool.false_xor, List.length_append] at h ⊢
  exact h

private theorem residual_length_parity (Z B R S : LowerPair)
    (h : LowerOther22Geometry Z B R S) :
    S.1.length % 2 = Z.1.length % 2 := by
  have hB : B = (Z.1 ++ [2], Z.2 ++ [3]) := by
    rw [h.birth]
    simp [lowerChild, h.normalizedZ]
  have hS : S = (Z.2 ++ [3,1], Z.1 ++ [2,2]) := by
    rw [h.stepS]
    simp [lowerChild, h.normalizedR, hB, List.append_assoc]
  have he := h.equalZ
  simp [hS, List.length_append, Nat.add_mod, he]

private theorem residual_local (Z B R S : LowerPair)
    (h : LowerOther22Geometry Z B R S) :
    lowerLocalLower S ([2],[1]) =
      (if Z.1.length % 2 = 1 then (-1 : ℝ) else 1) *
        lowerEndpoint (lowerChild S ([2],[1]))
          (decide (Z.1.length % 2 = 1)) := by
  have hp := residual_length_parity Z B R S h
  unfold lowerLocalLower
  simp only [h.normalizedS]
  rcases Nat.mod_two_eq_zero_or_one S.1.length with he | he
  · have hz : Z.1.length % 2 = 0 := by omega
    have ho : ¬ Z.1.length % 2 = 1 := by omega
    simp [he, hz, ho]
  · have hz : Z.1.length % 2 = 1 := by omega
    simp [he, hz]

private theorem residual_commonOdd (Z : LowerPair) (k : Fin 6)
    (hc : lowerHistoryContextFits Z (other22Context k)) :
    lowerHistoryCommonOdd Z (other22Context k) = decide (Z.1.length % 2 = 1) := by
  simp [lowerHistoryCommonOdd, other22Context]

private theorem residual_word_parity (k : Fin 6) :
    lowerHistoryWordParity (other22Context k) other22ResidualWords false =
      lowerHistoryWordParity (other22Context k) other22ResidualWords true := by
  simp [lowerHistoryWordParity, other22Context, other22ResidualWords,
    lowerHistoryPick]

private theorem residual_value_of_endpoint
    (hcf : ∀ (w : List ℕ+) (z : CertField), 0 ≤ certFieldVal z →
      certFieldVal (lowerHistoryCF w z) = prefixEval w (certFieldVal z))
    (Z B R S : LowerPair) (h : LowerOther22Geometry Z B R S)
    (k : Fin 6) (hc : lowerHistoryContextFits Z (other22Context k))
    (short₀ short₁ : Bool)
    (hw :
      lowerEndpointWords (lowerChild S ([2],[1]))
          (false.xor (lowerHistoryCommonOdd Z (other22Context k))) =
        ((Z.2 ++ other22ResidualWords.2) ++
            lowerEndpointSuffix (Z.2 ++ other22ResidualWords.2)
              (false.xor (lowerHistoryCommonOdd Z (other22Context k))) short₁,
          (Z.1 ++ other22ResidualWords.1) ++
            lowerEndpointSuffix (Z.1 ++ other22ResidualWords.1)
              (false.xor (lowerHistoryCommonOdd Z (other22Context k))) short₀)) :
    lowerLocalLower S ([2],[1]) =
      lowerHistoryValue Z (other22Context k)
        (lowerHistoryEndVal (other22Context k) other22ResidualWords false false short₀,
          lowerHistoryEndVal (other22Context k) other22ResidualWords false true short₁) := by
  have hQ := residual_child Z B R S h
  have hloc := residual_local Z B R S h
  have hco := residual_commonOdd Z k hc
  have hv := lowerHistory_endVals_value hcf Z (other22Context k) hc
    other22ResidualWords false short₀ short₁
  rw [hloc, hv]
  unfold lowerEndpoint
  rw [hQ] at hw ⊢
  simp [hco, other22ResidualWords] at hw ⊢
  rcases Nat.mod_two_eq_zero_or_one Z.1.length with he | he
  · simp [he] at hw ⊢
    rw [hw]
    abel
  · simp [he] at hw ⊢
    rw [hw]
    abel

theorem residual_cases
    (hwidth : LowerHistoryWidthLaw)
    (hcf : ∀ (w : List ℕ+) (z : CertField), 0 ≤ certFieldVal z →
      certFieldVal (lowerHistoryCF w z) = prefixEval w (certFieldVal z))
    (Z B R S : LowerPair) (hgeo : LowerOther22Geometry Z B R S)
    (k : Fin 6) (hc : lowerHistoryContextFits Z (other22Context k)) :
    ∃ z cs, (z,cs) ∈ lowerHistoryEndpointCases (other22Context k)
        other22ResidualWords false ∧
      lowerHistoryAtBase Z cs ∧
      lowerLocalLower S ([2],[1]) = lowerHistoryValue Z (other22Context k) z := by
  set C := other22Context k with hC
  set words := other22ResidualWords
  set base := Z
  have hp := residual_word_parity k
  have nat0 : lowerHistoryNatural C words false false = false := by
    fin_cases k <;> simp [lowerHistoryNatural, other22Context, other22ResidualWords,
      lowerHistoryPick, other22Paths, lowerHistoryWordParity] <;> decide
  have nat1 : lowerHistoryNatural C words false true = false := by
    fin_cases k <;> simp [lowerHistoryNatural, other22Context, other22ResidualWords,
      lowerHistoryPick, other22Paths, lowerHistoryWordParity] <;> decide
  have hpar := lowerHistory_physical_parity base C hc words hp
  have hs₀ := lowerHistory_natural_eq base C hc words false false
  have hs₁ := lowerHistory_natural_eq base C hc words false true
  have hn₀ : lowerHistoryNatural C words false false = false := nat0
  have hn₁ : lowerHistoryNatural C words false true = false := nat1
  have hQ : lowerChild S ([2],[1]) = (base.2 ++ words.2, base.1 ++ words.1) := by
    simpa [words, other22ResidualWords] using residual_child Z B R S hgeo
  have hs0p : lowerNaturalShort (base.1 ++ words.1)
      (false.xor (lowerHistoryCommonOdd base C)) = false := by
    simpa only [lowerHistoryPick, Bool.false_eq_true, ↓reduceIte, hn₀] using hs₀
  have hs1p : lowerNaturalShort (base.2 ++ words.2)
      (false.xor (lowerHistoryCommonOdd base C)) = false := by
    simpa only [lowerHistoryPick, ↓reduceIte, hn₁] using hs₁
  -- Residual words end in 1 and 2, so neither natural short applies.
  -- Select the physical orientation of S/21, including width ties.
  let e : List ℕ+ :=
    if xor (!false) (lowerHistoryWordParity C words false) then [3] else [1,3]
  let aux : LowerPair := (words.1 ++ e, words.2 ++ e)
  by_cases hwQ : lowerWidth (base.1 ++ words.1) ≤ lowerWidth (base.2 ++ words.2)
  · -- physical pair is left-wide or tied: shorten the 221 side if the 7/5 test holds
    let sh : Bool := decide
      (lowerWidth (base.2 ++ aux.2) ≤ (7/5:ℝ) * lowerWidth (base.1 ++ aux.1))
    let norm : CertBound := ⟨true,false,lowerHistoryWH words⟩
    let cut : CertBound :=
      ⟨false,false,lowerHistoryScaleThreshold (7/5) (lowerHistoryWH aux)⟩
    refine ⟨(lowerHistoryEndVal C words false false sh,
        lowerHistoryEndVal C words false true false),
      [norm, if sh then cut else lowerHistoryComplement cut], ?_, ?_, ?_⟩
    · unfold lowerHistoryEndpointCases
      rw [if_pos hp]
      dsimp only [lowerHistoryEqualCases]
      rw [if_neg (by simp [hn₀, hn₁])]
      simp only [List.mem_flatMap]
      refine ⟨(true, norm), by simp [lowerHistoryNormalCases, norm], ?_⟩
      simp only [List.mem_map]
      refine ⟨sh, by cases sh <;> simp, ?_⟩
      cases sh <;> simp [cut, aux, e]
    · apply at_pair
      · exact normal_true_le hwidth base words hwQ
      · by_cases hh : lowerWidth (base.2 ++ aux.2) ≤
            (7/5:ℝ) * lowerWidth (base.1 ++ aux.1)
        · simp [sh, hh, cut]
          exact M7ScaledCut14.scaled_upper_cut base aux |>.mpr hh
        · simp [sh, hh, cut]
          exact complement_upper_cut base aux hh
    · apply residual_value_of_endpoint hcf Z B R S hgeo k hc sh false
      have hlen : (Z.2 ++ [3,1,2]).length % 2 = (Z.1 ++ [2,2,1]).length % 2 := by
        simpa [base, words, other22ResidualWords] using hpar.symm
      have hQ' : lowerChild S ([2],[1]) = (Z.2 ++ [3,1,2], Z.1 ++ [2,2,1]) := by
        simpa [base, words, other22ResidualWords] using hQ
      rw [hQ', residual_endpointWords_eq _ _ hlen]
      have hwQ' : lowerWidth (Z.1 ++ [2,2,1]) ≤ lowerWidth (Z.2 ++ [3,1,2]) := by
        simpa [base, words, other22ResidualWords] using hwQ
      have hs0p' : lowerNaturalShort (Z.1 ++ [2,2,1])
          (lowerHistoryCommonOdd Z C) = false := by
        simpa [base, words, other22ResidualWords, Bool.false_xor] using hs0p
      have hs1p' : lowerNaturalShort (Z.2 ++ [3,1,2])
          (lowerHistoryCommonOdd Z C) = false := by
        simpa [base, words, other22ResidualWords, Bool.false_xor] using hs1p
      unfold lowerEqualWords lowerNormalize
      simp [hwQ', hs0p', hs1p', base, words, other22ResidualWords,
        Bool.false_xor, List.append_assoc]
      rw [hs0p', hs1p']
      simp [sh, aux, e, base, words, other22ResidualWords]
      congr 1
      have hx := residual_ext_eq Z k hc hp
      simp [other22ResidualWords] at hx
      simp [hx, hC]
      exact Iff.rfl
  · -- physical pair is strictly right-wide: shorten the 312 side if the 7/5 test holds
    have hwP : lowerWidth (base.2 ++ words.2) ≤ lowerWidth (base.1 ++ words.1) :=
      le_of_not_ge hwQ
    let sh : Bool := decide
      (lowerWidth (base.1 ++ aux.1) ≤ (7/5:ℝ) * lowerWidth (base.2 ++ aux.2))
    let norm : CertBound := ⟨false,false,lowerHistoryWH words⟩
    let cut : CertBound :=
      ⟨true,false,lowerHistoryScaleThreshold (5/7) (lowerHistoryWH aux)⟩
    refine ⟨(lowerHistoryEndVal C words false false false,
        lowerHistoryEndVal C words false true sh),
      [norm, if sh then cut else lowerHistoryComplement cut], ?_, ?_, ?_⟩
    · unfold lowerHistoryEndpointCases
      rw [if_pos hp]
      dsimp only [lowerHistoryEqualCases]
      rw [if_neg (by simp [hn₀, hn₁])]
      simp only [List.mem_flatMap]
      refine ⟨(false, norm), by simp [lowerHistoryNormalCases, norm], ?_⟩
      simp only [List.mem_map]
      refine ⟨sh, by cases sh <;> simp, ?_⟩
      cases sh <;> simp [cut, aux, e]
    · apply at_pair
      · exact normal_false hwidth base words hwP
      · by_cases hh : lowerWidth (base.1 ++ aux.1) ≤
            (7/5:ℝ) * lowerWidth (base.2 ++ aux.2)
        · simp [sh, hh, cut]
          exact M7ScaledCut14.scaled_lower_cut base aux |>.mpr hh
        · simp [sh, hh, cut]
          exact complement_lower_cut base aux hh
    · apply residual_value_of_endpoint hcf Z B R S hgeo k hc false sh
      have hlen : (Z.2 ++ [3,1,2]).length % 2 = (Z.1 ++ [2,2,1]).length % 2 := by
        simpa [base, words, other22ResidualWords] using hpar.symm
      have hQ' : lowerChild S ([2],[1]) = (Z.2 ++ [3,1,2], Z.1 ++ [2,2,1]) := by
        simpa [base, words, other22ResidualWords] using hQ
      rw [hQ', residual_endpointWords_eq _ _ hlen]
      have hwQ' : ¬ lowerWidth (Z.1 ++ [2,2,1]) ≤ lowerWidth (Z.2 ++ [3,1,2]) := by
        simpa [base, words, other22ResidualWords] using hwQ
      have hs0p' : lowerNaturalShort (Z.1 ++ [2,2,1])
          (lowerHistoryCommonOdd Z C) = false := by
        simpa [base, words, other22ResidualWords, Bool.false_xor] using hs0p
      have hs1p' : lowerNaturalShort (Z.2 ++ [3,1,2])
          (lowerHistoryCommonOdd Z C) = false := by
        simpa [base, words, other22ResidualWords, Bool.false_xor] using hs1p
      unfold lowerEqualWords lowerNormalize
      simp [hwQ', hs0p', hs1p', base, words, other22ResidualWords,
        Bool.false_xor, List.append_assoc]
      rw [hs0p', hs1p']
      simp [sh, aux, e, base, words, other22ResidualWords]
      have hmod : (Z.1.length + 3) % 2 = (Z.2.length + 3) % 2 := by
        simpa [base, words, other22ResidualWords, List.length_append] using hpar
      congr 1
      have hx := residual_ext_eq Z k hc hp
      simp [other22ResidualWords] at hx
      simp [hmod, hx, hC]
      exact Iff.rfl

end Freiman

-- Endpoint nonnegativity lemmas reused from accepted submission
-- d769562b-25b8-4db6-b0a7-965e4e05818d.
namespace M7Goodness14

private theorem prefix_nonneg (w : List ℕ+) (z : ℝ) (hz : 0 ≤ z) :
    0 ≤ prefixEval w z := by
  induction w with
  | nil => exact hz
  | cons a w ih =>
    simp only [prefixEval]
    positivity

private theorem tau_nonneg : 0 ≤ certFieldVal lowerHistoryTau := by
  have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  norm_num [certFieldVal, lowerHistoryTau]

private theorem endval_nonneg (C : LowerHistoryContext) (w : LowerPair)
    (upper side short : Bool) :
    0 ≤ certFieldVal (lowerHistoryEndVal C w upper side short) := by
  unfold lowerHistoryEndVal
  rw [lowerHistory_cf_value _ _ tau_nonneg]
  exact prefix_nonneg _ _ tau_nonneg

private theorem equal_nonneg (C : LowerHistoryContext) (w : LowerPair) (upper : Bool)
    (z : CertField × CertField) (cs : List CertBound)
    (hz : (z,cs) ∈ lowerHistoryEqualCases C w upper) :
    0 ≤ certFieldVal z.1 ∧ 0 ≤ certFieldVal z.2 := by
  by_cases hn : (lowerHistoryNatural C w upper false ||
      lowerHistoryNatural C w upper true) = true
  · simp only [lowerHistoryEqualCases, hn, ↓reduceIte,
      List.mem_singleton, Prod.mk.injEq] at hz
    rcases hz with ⟨rfl, rfl⟩
    exact ⟨endval_nonneg _ _ _ _ _, endval_nonneg _ _ _ _ _⟩
  · dsimp only [lowerHistoryEqualCases] at hz
    rw [if_neg hn] at hz
    simp only [List.mem_flatMap, List.mem_map] at hz
    obtain ⟨⟨wide,norm⟩, _, shortened, _, heq⟩ := hz
    cases heq
    exact ⟨endval_nonneg _ _ _ _ _, endval_nonneg _ _ _ _ _⟩

private theorem endpoint_nonneg (C : LowerHistoryContext) (w : LowerPair) (upper : Bool)
    (z : CertField × CertField) (cs : List CertBound)
    (hz : (z,cs) ∈ lowerHistoryEndpointCases C w upper) :
    0 ≤ certFieldVal z.1 ∧ 0 ≤ certFieldVal z.2 := by
  unfold lowerHistoryEndpointCases at hz
  split_ifs at hz with hp
  · exact equal_nonneg C w upper z cs hz
  · simp only [List.mem_flatMap, List.mem_map] at hz
    obtain ⟨⟨wide,norm⟩, _, ⟨v,bs⟩, hv, heq⟩ := hz
    cases heq
    split_ifs at hv
    · exact equal_nonneg _ _ _ _ _ hv
    · simp only [List.mem_singleton, Prod.mk.injEq] at hv
      rcases hv with ⟨rfl, rfl⟩
      exact ⟨endval_nonneg _ _ _ _ _, endval_nonneg _ _ _ _ _⟩

end M7Goodness14

open Freiman

theorem solution (Z B R S : LowerPair) (h : LowerOther22Geometry Z B R S)
    (k : Fin 6) (hc : lowerHistoryContextFits Z (other22Context k)) :
    other22EndpointRepresented Z (other22Context k) other22ResidualWords false
      (lowerLocalLower S ([2],[1])) := by
  have hwidth : LowerHistoryWidthLaw := fun base words =>
    lowerHistory_width_threshold base words
  have hcf : ∀ (w : List ℕ+) (z : CertField), 0 ≤ certFieldVal z →
      certFieldVal (lowerHistoryCF w z) = prefixEval w (certFieldVal z) :=
    fun w z hz => lowerHistory_cf_value w z hz
  obtain ⟨z,cs,hcase,hholds,hvalue⟩ :=
    residual_cases hwidth hcf Z B R S h k hc
  have hnonneg := M7Goodness14.endpoint_nonneg (other22Context k)
    other22ResidualWords false z cs hcase
  exact ⟨z,cs,hcase,hholds,hvalue,hnonneg.1,hnonneg.2⟩
