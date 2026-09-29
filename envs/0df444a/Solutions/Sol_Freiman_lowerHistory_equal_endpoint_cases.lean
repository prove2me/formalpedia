-- Prove2me | solution 1 for Freiman.lowerHistory_equal_endpoint_cases
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-13T08:27:34.163162+00:00
-- url     : https://prove2.me/submissions/b413ba29-7b7c-4c93-89f3-64e90df07a18

import Definitions.Def_Freiman_lowerHistoryVerification
import Theorems.Thm_Freiman_lowerHistory_cf_value
import Theorems.Thm_Freiman_lowerHistory_inv_value
import Theorems.Thm_Freiman_lowerHistory_sign_value
import Definitions.Def_Freiman_lowerHistoryAlgebra
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

private theorem lowerHistory_virtual_one_parity
    (C : LowerHistoryContext) (words : LowerPair) (wide : Bool)
    (hp : lowerHistoryWordParity C words false ≠
      lowerHistoryWordParity C words true) :
    lowerHistoryWordParity C
        (lowerHistorySet words wide
          (lowerHistoryPick words wide ++ [(1 : ℕ+)])) false =
      lowerHistoryWordParity C
        (lowerHistorySet words wide
          (lowerHistoryPick words wide ++ [(1 : ℕ+)])) true := by
  rcases C with ⟨⟨cl, cr⟩, ⟨pl, pr⟩⟩
  rcases words with ⟨wl, wr⟩
  cases wide <;>
    rcases Nat.mod_two_eq_zero_or_one wl.length with hl | hl <;>
    rcases Nat.mod_two_eq_zero_or_one wr.length with hr | hr <;>
    simp [lowerHistoryWordParity, lowerHistorySet, lowerHistoryPick,
      List.length_append, Nat.add_mod, hl, hr] at hp ⊢
  all_goals cases pl <;> cases pr <;> simp_all

private theorem lowerHistory_endpoint_from_words
    (hcf : ∀ (w : List ℕ+) (z : CertField), 0 ≤ certFieldVal z →
      certFieldVal (lowerHistoryCF w z) = prefixEval w (certFieldVal z))
    (base : LowerPair) (C : LowerHistoryContext)
    (hc : lowerHistoryContextFits base C) (words : LowerPair)
    (upper short₀ short₁ : Bool)
    (hw :
      lowerEndpointWords (lowerHistoryAppend base words)
          (upper.xor (lowerHistoryCommonOdd base C)) =
        ((base.1 ++ words.1) ++
            lowerEndpointSuffix (base.1 ++ words.1)
              (upper.xor (lowerHistoryCommonOdd base C)) short₀,
          (base.2 ++ words.2) ++
            lowerEndpointSuffix (base.2 ++ words.2)
              (upper.xor (lowerHistoryCommonOdd base C)) short₁)) :
    lowerHistoryEndpointReal base C words upper =
      lowerHistoryValue base C
        (lowerHistoryEndVal C words upper false short₀,
          lowerHistoryEndVal C words upper true short₁) := by
  rw [lowerHistory_endVals_value hcf base C hc words upper short₀ short₁]
  unfold lowerHistoryEndpointReal lowerHistoryAppend
  change (if lowerHistoryCommonOdd base C then -1 else 1) *
      (4 + prefixEval
        (lowerEndpointWords (base.1 ++ words.1, base.2 ++ words.2)
          (upper.xor (lowerHistoryCommonOdd base C))).1 lowerTau +
        prefixEval
        (lowerEndpointWords (base.1 ++ words.1, base.2 ++ words.2)
          (upper.xor (lowerHistoryCommonOdd base C))).2 lowerTau) = _
  have hw' : lowerEndpointWords (base.1 ++ words.1, base.2 ++ words.2)
      (upper.xor (lowerHistoryCommonOdd base C)) =
        ((base.1 ++ words.1) ++
            lowerEndpointSuffix (base.1 ++ words.1)
              (upper.xor (lowerHistoryCommonOdd base C)) short₀,
          (base.2 ++ words.2) ++
            lowerEndpointSuffix (base.2 ++ words.2)
              (upper.xor (lowerHistoryCommonOdd base C)) short₁) := by
    simpa only [lowerHistoryAppend] using hw
  rw [hw']

end Freiman


open Freiman
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 0
set_option maxRecDepth 10000

namespace Freiman

private theorem at_pair {base : LowerPair} {a b : CertBound}
    (ha : lowerHistoryAtBase base [a]) (hb : lowerHistoryAtBase base [b]) :
    lowerHistoryAtBase base [a,b] := by
  simpa [lowerHistoryAtBase, lowerHistoryConditions] using And.intro ha hb

private theorem normal_false (hwidth : LowerHistoryWidthLaw)
    (base words : LowerPair)
    (hw : lowerWidth (base.2 ++ words.2) ≤ lowerWidth (base.1 ++ words.1)) :
    lowerHistoryAtBase base [⟨false,false,lowerHistoryWH words⟩] :=
  (hwidth base words).1.mp hw

private theorem normal_true (hwidth : LowerHistoryWidthLaw)
    (base words : LowerPair)
    (hw : ¬ lowerWidth (base.2 ++ words.2) ≤ lowerWidth (base.1 ++ words.1)) :
    lowerHistoryAtBase base [⟨true,false,lowerHistoryWH words⟩] := by
  have hn : ¬ lowerHistoryAtBase base [⟨false,true,lowerHistoryWH words⟩] := by
    rw [← (hwidth base words).2]
    exact not_lt_of_ge (le_of_not_ge hw)
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

private theorem equal_endpoint_cases_core (hwidth : LowerHistoryWidthLaw)
    (hcf : ∀ (w : List ℕ+) (z : CertField), 0 ≤ certFieldVal z →
      certFieldVal (lowerHistoryCF w z) = prefixEval w (certFieldVal z))
    (base : LowerPair) (C : LowerHistoryContext)
    (hc : lowerHistoryContextFits base C) (words : LowerPair) (upper : Bool)
    (hp : lowerHistoryWordParity C words false =
      lowerHistoryWordParity C words true) :
    ∃ z cs, (z,cs) ∈ lowerHistoryEndpointCases C words upper ∧
      lowerHistoryAtBase base cs ∧
      lowerHistoryEndpointReal base C words upper = lowerHistoryValue base C z := by
  let n₀ := lowerHistoryNatural C words upper false
  let n₁ := lowerHistoryNatural C words upper true
  have hpar := lowerHistory_physical_parity base C hc words hp
  have hs₀ := lowerHistory_natural_eq base C hc words upper false
  have hs₁ := lowerHistory_natural_eq base C hc words upper true
  generalize hn₀ : lowerHistoryNatural C words upper false = b₀ at hs₀
  generalize hn₁ : lowerHistoryNatural C words upper true = b₁ at hs₁
  cases b₀ <;> cases b₁
  · -- no natural shortening: select the actual normalization and auxiliary cut
    let e : List ℕ+ :=
      if xor (!upper) (lowerHistoryWordParity C words false) then [3] else [1,3]
    let aux : LowerPair := (words.1 ++ e, words.2 ++ e)
    by_cases hw : lowerWidth (base.2 ++ words.2) ≤ lowerWidth (base.1 ++ words.1)
    · let sh : Bool := decide
        (lowerWidth (base.1 ++ aux.1) ≤ (7/5:ℝ) * lowerWidth (base.2 ++ aux.2))
      let norm : CertBound := ⟨false,false,lowerHistoryWH words⟩
      let cut : CertBound :=
        ⟨true,false,lowerHistoryScaleThreshold (5/7) (lowerHistoryWH aux)⟩
      refine ⟨(lowerHistoryEndVal C words upper false false,
          lowerHistoryEndVal C words upper true sh),
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
        · exact normal_false hwidth base words hw
        · by_cases hh : lowerWidth (base.1 ++ aux.1) ≤
              (7/5:ℝ) * lowerWidth (base.2 ++ aux.2)
          · simp [sh, hh, cut]
            exact M7ScaledCut14.scaled_lower_cut base aux |>.mpr hh
          · simp [sh, hh, cut]
            exact complement_lower_cut base aux hh
      · apply lowerHistory_endpoint_from_words hcf base C hc words upper false sh
        simp only [lowerHistoryAppend]
        unfold lowerEndpointWords
        rw [if_pos hpar]
        have hs0p : lowerNaturalShort (base.1 ++ words.1)
            (upper.xor (lowerHistoryCommonOdd base C)) = false := by
          simpa only [lowerHistoryPick, Bool.false_eq_true, ↓reduceIte] using hs₀
        have hs1p : lowerNaturalShort (base.2 ++ words.2)
            (upper.xor (lowerHistoryCommonOdd base C)) = false := by
          simpa only [lowerHistoryPick, ↓reduceIte] using hs₁
        have he0 := lowerHistory_endpointSuffix_eq base C hc words upper false false
        have he1 := lowerHistory_endpointSuffix_eq base C hc words upper true false
        have he0' : (if ((base.1 ++ words.1).length % 2 = 0) =
              !(upper.xor (lowerHistoryCommonOdd base C)) then [3] else [1,3]) = e := by
          simpa [lowerEndpointSuffix, lowerHistoryPick, e] using he0
        have he1' : (if ((base.2 ++ words.2).length % 2 = 0) =
              !(upper.xor (lowerHistoryCommonOdd base C)) then [3] else [1,3]) = e := by
          simpa [lowerEndpointSuffix, lowerHistoryPick, e, hp] using he1
        unfold lowerEqualWords lowerNormalize
        simp only [hw, ↓reduceIte, Prod.fst, Prod.snd]
        rw [hs0p, hs1p]
        simp only [Bool.not_false, Bool.true_and, Bool.false_or, Bool.not_true,
          Bool.false_and]
        rw [he0']
        simp only [List.append_assoc]
        rfl
    · let sh : Bool := decide
        (lowerWidth (base.2 ++ aux.2) ≤ (7/5:ℝ) * lowerWidth (base.1 ++ aux.1))
      let norm : CertBound := ⟨true,false,lowerHistoryWH words⟩
      let cut : CertBound :=
        ⟨false,false,lowerHistoryScaleThreshold (7/5) (lowerHistoryWH aux)⟩
      refine ⟨(lowerHistoryEndVal C words upper false sh,
          lowerHistoryEndVal C words upper true false),
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
        · exact normal_true hwidth base words hw
        · by_cases hh : lowerWidth (base.2 ++ aux.2) ≤
              (7/5:ℝ) * lowerWidth (base.1 ++ aux.1)
          · simp [sh, hh, cut]
            exact M7ScaledCut14.scaled_upper_cut base aux |>.mpr hh
          · simp [sh, hh, cut]
            exact complement_upper_cut base aux hh
      · apply lowerHistory_endpoint_from_words hcf base C hc words upper sh false
        simp only [lowerHistoryAppend]
        unfold lowerEndpointWords
        rw [if_pos hpar]
        have hs0p : lowerNaturalShort (base.1 ++ words.1)
            (upper.xor (lowerHistoryCommonOdd base C)) = false := by
          simpa only [lowerHistoryPick, Bool.false_eq_true, ↓reduceIte] using hs₀
        have hs1p : lowerNaturalShort (base.2 ++ words.2)
            (upper.xor (lowerHistoryCommonOdd base C)) = false := by
          simpa only [lowerHistoryPick, ↓reduceIte] using hs₁
        have he0 := lowerHistory_endpointSuffix_eq base C hc words upper false false
        have he1 := lowerHistory_endpointSuffix_eq base C hc words upper true false
        have he0' : (if ((base.1 ++ words.1).length % 2 = 0) =
              !(upper.xor (lowerHistoryCommonOdd base C)) then [3] else [1,3]) = e := by
          simpa [lowerEndpointSuffix, lowerHistoryPick, e] using he0
        have he1' : (if ((base.2 ++ words.2).length % 2 = 0) =
              !(upper.xor (lowerHistoryCommonOdd base C)) then [3] else [1,3]) = e := by
          simpa [lowerEndpointSuffix, lowerHistoryPick, e, hp] using he1
        unfold lowerEqualWords lowerNormalize
        simp only [hw, ↓reduceIte, Prod.fst, Prod.snd]
        rw [hs1p, hs0p]
        simp only [Bool.not_false, Bool.true_and, Bool.false_or, Bool.not_true,
          Bool.false_and]
        rw [he1']
        simp only [List.append_assoc]
        rfl
  all_goals
    refine ⟨(lowerHistoryEndVal C words upper false
          (lowerHistoryNatural C words upper false),
        lowerHistoryEndVal C words upper true
          (lowerHistoryNatural C words upper true)), [], ?_, by simp
          [lowerHistoryAtBase, lowerHistoryConditions], ?_⟩
    · unfold lowerHistoryEndpointCases
      rw [if_pos hp]
      simp [lowerHistoryEqualCases, hn₀, hn₁]
    · apply lowerHistory_endpoint_from_words hcf base C hc words upper
          (lowerHistoryNatural C words upper false)
          (lowerHistoryNatural C words upper true)
      simp only [lowerHistoryAppend]
      unfold lowerEndpointWords
      rw [if_pos hpar]
      have hs0p := hs₀
      have hs1p := hs₁
      simp only [lowerHistoryPick, Bool.false_eq_true, ↓reduceIte] at hs0p
      simp only [lowerHistoryPick, ↓reduceIte] at hs1p
      unfold lowerEqualWords lowerNormalize
      by_cases hw : lowerWidth (base.2 ++ words.2) ≤ lowerWidth (base.1 ++ words.1)
      · simp only [hw, ↓reduceIte, Prod.fst, Prod.snd]
        rw [hs0p, hs1p]
        simp [hn₀, hn₁, List.append_assoc]
      · simp only [hw, ↓reduceIte, Prod.fst, Prod.snd]
        rw [hs1p, hs0p]
        simp [hn₀, hn₁, List.append_assoc]


end Freiman

theorem solution (hwidth : LowerHistoryWidthLaw) (hcf : ∀ (w : List ℕ+) (z : CertField), 0 ≤ certFieldVal z → certFieldVal (lowerHistoryCF w z) = prefixEval w (certFieldVal z))
    (base : LowerPair) (C : LowerHistoryContext) (hc : lowerHistoryContextFits base C) (words : LowerPair) (upper : Bool)
    (hp : lowerHistoryWordParity C words false = lowerHistoryWordParity C words true) :
    ∃ z cs, (z,cs) ∈ lowerHistoryEndpointCases C words upper ∧ lowerHistoryAtBase base cs ∧
      lowerHistoryEndpointReal base C words upper = lowerHistoryValue base C z := by
  exact Freiman.equal_endpoint_cases_core hwidth hcf base C hc words upper hp

#print axioms solution
