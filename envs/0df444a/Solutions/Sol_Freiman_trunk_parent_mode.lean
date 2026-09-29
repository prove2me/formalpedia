-- Prove2me | solution 1 for Freiman.trunk_parent_mode
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-13T12:53:43.710297+00:00
-- url     : https://prove2.me/submissions/9e92fa8a-d4b0-4927-bf5e-9b4fb1c2e492

import Definitions.Def_Freiman_lowerHistoryVerification
import Theorems.Thm_Freiman_lowerHistory_cf_value
import Theorems.Thm_Freiman_lowerHistory_inv_value
import Theorems.Thm_Freiman_lowerHistory_sign_value
import Theorems.Thm_Freiman_prefixEval_difference
import Theorems.Thm_Freiman_continuant_denominator_pos
import Mathlib.Tactic

import Definitions.Def_Freiman_trunkGeometry
import Theorems.Thm_Freiman_lowerHistory_width_threshold
import Theorems.Thm_Freiman_lowerHistory_greater_from_sign

namespace TrunkParentAdapt

private def lowerHistoryNormalCases (w : Freiman.LowerPair) : List (Bool × Freiman.CertBound) :=
  [(false,⟨false,false,Freiman.lowerHistoryWH w⟩),
   (true,⟨true,true,Freiman.lowerHistoryWH w⟩)]
private def lowerHistoryEqualCases (C : Freiman.LowerHistoryContext) (w : Freiman.LowerPair)
    (upper : Bool) : List Freiman.LowerHistoryEndCase :=
  let n := (Freiman.lowerHistoryNatural C w upper false, Freiman.lowerHistoryNatural C w upper true)
  if n.1 || n.2 then
    [((Freiman.lowerHistoryEndVal C w upper false n.1, Freiman.lowerHistoryEndVal C w upper true n.2),[])]
  else
    let e : List ℕ+ := if xor (!upper) (Freiman.lowerHistoryWordParity C w false) then [3] else [1,3]
    let aux := Freiman.lowerHistoryWH (w.1++e,w.2++e)
    (lowerHistoryNormalCases w).flatMap fun (wide,norm) =>
      let cut : Freiman.CertBound := if wide then ⟨false,false,Freiman.lowerHistoryScaleThreshold (7/5) aux⟩
        else ⟨true,false,Freiman.lowerHistoryScaleThreshold (5/7) aux⟩
      [false,true].map fun shortened =>
        ((Freiman.lowerHistoryEndVal C w upper false (shortened && wide),
          Freiman.lowerHistoryEndVal C w upper true (shortened && !wide)),
          [norm,if shortened then cut else Freiman.lowerHistoryComplement cut])
private def lowerHistoryEndpointCases (C : Freiman.LowerHistoryContext) (w : Freiman.LowerPair)
    (upper : Bool) : List Freiman.LowerHistoryEndCase :=
  if Freiman.lowerHistoryWordParity C w false = Freiman.lowerHistoryWordParity C w true then
    lowerHistoryEqualCases C w upper
  else (lowerHistoryNormalCases w).flatMap fun (wide,norm) =>
    let vs := if upper = !(Freiman.lowerHistoryWordParity C w wide) then
      lowerHistoryEqualCases C (Freiman.lowerHistorySet w wide (Freiman.lowerHistoryPick w wide ++ [1])) upper
    else [((Freiman.lowerHistoryEndVal C w upper false (Freiman.lowerHistoryNatural C w upper false),
            Freiman.lowerHistoryEndVal C w upper true (Freiman.lowerHistoryNatural C w upper true)),[])]
    vs.map fun (v,cs) => (v,norm::cs)


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
    lowerHistoryAtBase base [⟨true,true,lowerHistoryWH words⟩] := by
  have hn : ¬ lowerHistoryAtBase base [⟨false,false,lowerHistoryWH words⟩] := by
    rw [← (hwidth base words).1]
    exact hw
  simp only [lowerHistoryAtBase, lowerHistoryConditions, List.mem_singleton,
    forall_eq, certBoundHolds, Bool.false_eq_true, ↓reduceIte] at hn ⊢
  exact lt_of_not_ge hn

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

private theorem lowerHistory_equal_endpoint_cases (hwidth : LowerHistoryWidthLaw)
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
      let norm : CertBound := ⟨true,true,lowerHistoryWH words⟩
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

open Freiman

namespace Freiman

private lemma lowerHistory_suffix3_snoc (u : List ℕ+) (a : ℕ+) :
    ([3] : List ℕ+).IsSuffix (u ++ [a]) ↔ a = 3 := by
  simp [List.IsSuffix, eq_comm]

private lemma lowerHistory_suffix31_snoc (u : List ℕ+) (a : ℕ+) :
    ([3, 1] : List ℕ+).IsSuffix (u ++ [a]) ↔
      a = 1 ∧ ([3] : List ℕ+).IsSuffix u := by
  constructor
  · intro h
    obtain ⟨t, ht⟩ := h
    have := congrArg List.reverse ht
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil] at this
    simp at this
    rcases this with ⟨ha, hu⟩
    subst a
    refine ⟨rfl, t, ?_⟩
    have hr := congrArg List.reverse hu
    simpa using hr
  · rintro ⟨rfl, t, rfl⟩
    exact ⟨t, by simp⟩

private lemma lowerHistory_suffix_context_append (u v w : List ℕ+)
    (h3 : ([3] : List ℕ+).IsSuffix u ↔ ([3] : List ℕ+).IsSuffix v)
    (h31 : ([3,1] : List ℕ+).IsSuffix u ↔ ([3,1] : List ℕ+).IsSuffix v) :
    (([3] : List ℕ+).IsSuffix (u ++ w) ↔ ([3] : List ℕ+).IsSuffix (v ++ w)) ∧
    (([3,1] : List ℕ+).IsSuffix (u ++ w) ↔ ([3,1] : List ℕ+).IsSuffix (v ++ w)) := by
  induction w generalizing u v with
  | nil => simpa using And.intro h3 h31
  | cons a w ih =>
      rw [show u ++ a :: w = (u ++ [a]) ++ w by simp,
          show v ++ a :: w = (v ++ [a]) ++ w by simp]
      apply ih
      · simp only [lowerHistory_suffix3_snoc]
      · simp only [lowerHistory_suffix31_snoc]
        exact and_congr Iff.rfl h3

private lemma lowerHistory_context_suffix_append (base : LowerPair) (C : LowerHistoryContext)
    (hc : lowerHistoryContextFits base C) (words : LowerPair) (side : Bool) :
    (([3] : List ℕ+).IsSuffix
          (lowerHistoryPick base side ++ lowerHistoryPick words side) ↔
      ([3] : List ℕ+).IsSuffix
          (lowerHistoryPick C.words side ++ lowerHistoryPick words side)) ∧
    (([3,1] : List ℕ+).IsSuffix
          (lowerHistoryPick base side ++ lowerHistoryPick words side) ↔
      ([3,1] : List ℕ+).IsSuffix
          (lowerHistoryPick C.words side ++ lowerHistoryPick words side)) := by
  rcases side with _ | _
  · exact lowerHistory_suffix_context_append _ _ _ hc.1.2.1 hc.1.2.2
  · exact lowerHistory_suffix_context_append _ _ _ hc.2.1.2.1 hc.2.1.2.2

private lemma lowerHistory_prefixEval_append (u v : List ℕ+) (x : ℝ) :
    prefixEval (u ++ v) x = prefixEval u (prefixEval v x) := by
  induction u with
  | nil => rfl
  | cons a u ih => simp only [List.cons_append, prefixEval, ih]

private lemma lowerHistory_odd_append (u v : List ℕ+) :
    decide ((u ++ v).length % 2 = 1) =
      (decide (u.length % 2 = 1)).xor (decide (v.length % 2 = 1)) := by
  simp only [List.length_append]
  by_cases hu : u.length % 2 = 1 <;>
    by_cases hv : v.length % 2 = 1
  all_goals have hsum : (u.length + v.length) % 2 = 1 ↔
      ¬ (u.length % 2 = 1 ↔ v.length % 2 = 1) := by omega
  all_goals simp [hu, hv, hsum]

private lemma lowerHistory_even_not_odd (u : List ℕ+) :
    decide (u.length % 2 = 0) = !(decide (u.length % 2 = 1)) := by
  by_cases he : u.length % 2 = 0
  · have ho : ¬ u.length % 2 = 1 := by omega
    simp [he, ho]
  · have ho : u.length % 2 = 1 := by omega
    simp [he, ho]

private lemma lowerHistory_even_iff_not_odd (u : List ℕ+) :
    (u.length % 2 = 0) ↔ decide (u.length % 2 = 1) = false := by
  by_cases he : u.length % 2 = 0
  · have ho : ¬ u.length % 2 = 1 := by omega
    simp [he, ho]
  · have ho : u.length % 2 = 1 := by omega
    simp [he, ho]

private lemma lowerHistory_xor_transfer (a b c d w : Bool)
    (h : a.xor c = b.xor d) :
    b.xor w = (a.xor c).xor (d.xor w) := by
  rcases a with _ | _ <;> rcases b with _ | _ <;>
    rcases c with _ | _ <;> rcases d with _ | _ <;>
    rcases w with _ | _ <;> simp_all

private lemma lowerHistory_physical_odd (base : LowerPair) (C : LowerHistoryContext)
    (hc : lowerHistoryContextFits base C) (words : LowerPair) (side : Bool) :
    decide ((lowerHistoryPick base side ++ lowerHistoryPick words side).length % 2 = 1) =
      (lowerHistoryCommonOdd base C).xor (lowerHistoryWordParity C words side) := by
  rcases side with _ | _
  · rw [lowerHistory_odd_append]
    simp [lowerHistoryPick, lowerHistoryCommonOdd, lowerHistoryWordParity]
  · have hpar := hc.2.2
    rw [lowerHistory_odd_append]
    simp only [lowerHistoryCommonOdd, lowerHistoryPick, lowerHistoryWordParity] at hpar ⊢
    exact lowerHistory_xor_transfer _ _ _ _ _ hpar

private lemma lowerHistory_tail3_physical (base : LowerPair) (C : LowerHistoryContext)
    (hc : lowerHistoryContextFits base C) (words : LowerPair) (upper side : Bool) :
    (((lowerHistoryPick base side ++ lowerHistoryPick words side).length % 2 = 0) =
        (!(upper.xor (lowerHistoryCommonOdd base C)))) ↔
      ((!upper).xor (lowerHistoryWordParity C words side)) := by
  have ho := lowerHistory_physical_odd base C hc words side
  rw [lowerHistory_even_iff_not_odd, ho]
  rcases upper with _ | _ <;>
    rcases lowerHistoryCommonOdd base C with _ | _ <;>
    rcases lowerHistoryWordParity C words side with _ | _ <;> decide

private lemma lowerHistory_xor_left_injective (c : Bool) : Function.Injective c.xor := by
  rcases c with _ | _ <;> intro a b h <;>
    rcases a with _ | _ <;> rcases b with _ | _ <;> simp_all

private lemma lowerHistory_mixed_physical_parity (base : LowerPair) (C : LowerHistoryContext)
    (hc : lowerHistoryContextFits base C) (words : LowerPair)
    (hp : lowerHistoryWordParity C words false ≠ lowerHistoryWordParity C words true) :
    (base.1 ++ words.1).length % 2 ≠ (base.2 ++ words.2).length % 2 := by
  have h0 := lowerHistory_physical_odd base C hc words false
  have h1 := lowerHistory_physical_odd base C hc words true
  simp [lowerHistoryPick] at h0 h1
  intro hlen
  apply hp
  apply lowerHistory_xor_left_injective (lowerHistoryCommonOdd base C)
  rw [← h0, ← h1]
  simp only [List.length_append] at hlen
  rw [hlen]

private lemma lowerHistory_normal_left (hwidth : LowerHistoryWidthLaw)
    (base words : LowerPair)
    (hw : lowerWidth (base.2 ++ words.2) ≤ lowerWidth (base.1 ++ words.1)) :
    lowerHistoryAtBase base [⟨false,false,lowerHistoryWH words⟩] :=
  (hwidth base words).1.mp hw

private lemma lowerHistory_normal_right (hwidth : LowerHistoryWidthLaw)
    (base words : LowerPair)
    (hw : ¬ lowerWidth (base.2 ++ words.2) ≤ lowerWidth (base.1 ++ words.1)) :
    lowerHistoryAtBase base [⟨true,true,lowerHistoryWH words⟩] := by
  have hn : ¬ lowerHistoryAtBase base [⟨false,false,lowerHistoryWH words⟩] := by
    rw [← (hwidth base words).1]
    exact hw
  simp only [lowerHistoryAtBase, lowerHistoryConditions, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq, certBoundHolds] at hn ⊢
  exact lt_of_not_ge hn

private lemma lowerHistory_virtual_upper_iff (base : LowerPair) (C : LowerHistoryContext)
    (hc : lowerHistoryContextFits base C) (words : LowerPair) (upper side : Bool) :
    upper.xor (lowerHistoryCommonOdd base C) =
        decide ((lowerHistoryPick base side ++ lowerHistoryPick words side).length % 2 = 0) ↔
      upper = !(lowerHistoryWordParity C words side) := by
  have ho := lowerHistory_physical_odd base C hc words side
  rw [lowerHistory_even_not_odd, ho]
  rcases upper with _ | _ <;>
    rcases lowerHistoryCommonOdd base C with _ | _ <;>
    rcases lowerHistoryWordParity C words side with _ | _ <;> decide

private lemma lowerHistory_virtual_one_parity_mixed (C : LowerHistoryContext) (words : LowerPair)
    (wide : Bool)
    (hp : lowerHistoryWordParity C words false ≠ lowerHistoryWordParity C words true) :
    lowerHistoryWordParity C
        (lowerHistorySet words wide (lowerHistoryPick words wide ++ [1])) false =
      lowerHistoryWordParity C
        (lowerHistorySet words wide (lowerHistoryPick words wide ++ [1])) true := by
  rcases C with ⟨⟨cl, cr⟩, ⟨pl, pr⟩⟩
  rcases words with ⟨wl, wr⟩
  cases wide <;>
    rcases Nat.mod_two_eq_zero_or_one wl.length with hl | hl <;>
    rcases Nat.mod_two_eq_zero_or_one wr.length with hr | hr <;>
    simp [lowerHistoryWordParity, lowerHistorySet, lowerHistoryPick,
      List.length_append, Nat.add_mod, hl, hr] at hp ⊢
  all_goals cases pl <;> cases pr <;> simp_all

private lemma lowerHistory_equal_physical_parity (base : LowerPair) (C : LowerHistoryContext)
    (hc : lowerHistoryContextFits base C) (words : LowerPair)
    (hp : lowerHistoryWordParity C words false = lowerHistoryWordParity C words true) :
    (base.1 ++ words.1).length % 2 = (base.2 ++ words.2).length % 2 := by
  have h0 := lowerHistory_physical_odd base C hc words false
  have h1 := lowerHistory_physical_odd base C hc words true
  simp [lowerHistoryPick] at h0 h1
  rw [hp] at h0
  have hd : decide ((base.1.length + words.1.length) % 2 = 1) =
      decide ((base.2.length + words.2.length) % 2 = 1) := h0.trans h1.symm
  simp only [List.length_append]
  rcases Nat.mod_two_eq_zero_or_one (base.1.length + words.1.length) with hl | hl <;>
    rcases Nat.mod_two_eq_zero_or_one (base.2.length + words.2.length) with hr | hr
  all_goals simp [hl, hr] at hd ⊢

private lemma lowerHistory_virtual_endpoint_eq
    (base : LowerPair) (C : LowerHistoryContext) (hc : lowerHistoryContextFits base C)
    (words : LowerPair) (upper wide : Bool)
    (hp : lowerHistoryWordParity C words false ≠ lowerHistoryWordParity C words true)
    (hwide : if wide then
        ¬ lowerWidth (base.2 ++ words.2) ≤ lowerWidth (base.1 ++ words.1)
      else lowerWidth (base.2 ++ words.2) ≤ lowerWidth (base.1 ++ words.1))
    (hvirtual : upper = !(lowerHistoryWordParity C words wide)) :
    lowerHistoryEndpointReal base C words upper =
      lowerHistoryEndpointReal base C
        (lowerHistorySet words wide (lowerHistoryPick words wide ++ [1])) upper := by
  let vwords := lowerHistorySet words wide (lowerHistoryPick words wide ++ [1])
  have hpv : lowerHistoryWordParity C vwords false =
      lowerHistoryWordParity C vwords true :=
    lowerHistory_virtual_one_parity_mixed C words wide hp
  have hpar := lowerHistory_mixed_physical_parity base C hc words hp
  have hparv := lowerHistory_equal_physical_parity base C hc vwords hpv
  have hv := (lowerHistory_virtual_upper_iff base C hc words upper wide).mpr hvirtual
  have hwords : lowerEndpointWords (lowerHistoryAppend base words)
        (upper.xor (lowerHistoryCommonOdd base C)) =
      lowerEndpointWords (lowerHistoryAppend base vwords)
        (upper.xor (lowerHistoryCommonOdd base C)) := by
    unfold lowerHistoryAppend lowerEndpointWords
    rw [if_neg hpar]
    simp only [Prod.fst, Prod.snd]
    rcases wide with _ | _
    · simp only [Bool.false_eq_true, if_false] at hwide
      simp [lowerHistoryPick] at hv
      have hv' : upper.xor (lowerHistoryCommonOdd base C) =
          decide ((base.1 ++ words.1).length % 2 = 0) := by
        simpa only [List.length_append] using hv
      rw [if_pos hwide, if_pos hv']
      simp only [vwords, lowerHistorySet, lowerHistoryPick, Bool.false_eq_true,
        if_false, Prod.fst, Prod.snd] at hparv ⊢
      rw [if_pos hparv]
      rw [if_pos hwide]
      simp only [List.append_assoc]
    · simp only [Bool.true_eq, if_true] at hwide
      simp [lowerHistoryPick] at hv
      have hv' : upper.xor (lowerHistoryCommonOdd base C) =
          decide ((base.2 ++ words.2).length % 2 = 0) := by
        simpa only [List.length_append] using hv
      rw [if_neg hwide, if_pos hv']
      simp only [vwords, lowerHistorySet, lowerHistoryPick, Bool.true_eq,
        if_true, Prod.fst, Prod.snd] at hparv ⊢
      rw [if_pos hparv]
      rw [if_neg hwide]
      simp only [List.append_assoc]
  unfold lowerHistoryEndpointReal lowerEndpoint
  rw [hwords]

private lemma lowerHistory_natural_endpoint_value
    (hcf : ∀ (w : List ℕ+) (z : CertField), 0 ≤ certFieldVal z →
      certFieldVal (lowerHistoryCF w z) = prefixEval w (certFieldVal z))
    (base : LowerPair) (C : LowerHistoryContext) (hc : lowerHistoryContextFits base C)
    (words : LowerPair) (upper wide : Bool)
    (hp : lowerHistoryWordParity C words false ≠ lowerHistoryWordParity C words true) :
    (if wide then ¬ lowerWidth (base.2 ++ words.2) ≤ lowerWidth (base.1 ++ words.1)
      else lowerWidth (base.2 ++ words.2) ≤ lowerWidth (base.1 ++ words.1)) →
    upper ≠ !(lowerHistoryWordParity C words wide) →
    lowerHistoryEndpointReal base C words upper =
      lowerHistoryValue base C
        (lowerHistoryEndVal C words upper false (lowerHistoryNatural C words upper false),
          lowerHistoryEndVal C words upper true (lowerHistoryNatural C words upper true)) := by
  intro hwide hnatural
  have hpar := lowerHistory_mixed_physical_parity base C hc words hp
  have hn0 := lowerHistory_natural_eq base C hc words upper false
  have hn1 := lowerHistory_natural_eq base C hc words upper true
  rw [lowerHistory_endVals_value hcf base C hc]
  unfold lowerHistoryEndpointReal lowerHistoryAppend lowerEndpoint lowerEndpointWords
  rw [if_neg hpar]
  simp only [Prod.fst, Prod.snd]
  rcases wide with _ | _
  · simp only [Bool.false_eq_true, if_false] at hwide
    have hv := lowerHistory_virtual_upper_iff base C hc words upper false
    simp [lowerHistoryPick] at hv
    rw [if_pos hwide]
    simp only [List.length_append]
    rw [if_neg (fun h => hnatural (hv.mp h))]
    unfold lowerNaturalWords
    simp [lowerHistoryPick] at hn0 hn1
    rw [hn0, hn1]
  · simp only [Bool.true_eq, if_true] at hwide
    have hv := lowerHistory_virtual_upper_iff base C hc words upper true
    simp [lowerHistoryPick] at hv
    rw [if_neg hwide]
    simp only [List.length_append]
    rw [if_neg (fun h => hnatural (hv.mp h))]
    unfold lowerNaturalWords
    simp [lowerHistoryPick] at hn0 hn1
    rw [hn0, hn1]

private theorem lowerHistory_mixed_endpoint_cases_from_equal
    (hequal : ∀ (base : LowerPair) (C : LowerHistoryContext),
      lowerHistoryContextFits base C → ∀ (words : LowerPair) (upper : Bool),
      lowerHistoryWordParity C words false = lowerHistoryWordParity C words true →
      ∃ z cs, (z,cs) ∈ lowerHistoryEndpointCases C words upper ∧
        lowerHistoryAtBase base cs ∧
        lowerHistoryEndpointReal base C words upper = lowerHistoryValue base C z)
    (hwidth : LowerHistoryWidthLaw)
    (hcf : ∀ (w : List ℕ+) (z : CertField), 0 ≤ certFieldVal z →
      certFieldVal (lowerHistoryCF w z) = prefixEval w (certFieldVal z))
    (base : LowerPair) (C : LowerHistoryContext) (hc : lowerHistoryContextFits base C)
    (words : LowerPair) (upper : Bool)
    (hp : lowerHistoryWordParity C words false ≠ lowerHistoryWordParity C words true) :
    ∃ z cs, (z,cs) ∈ lowerHistoryEndpointCases C words upper ∧
      lowerHistoryAtBase base cs ∧
      lowerHistoryEndpointReal base C words upper = lowerHistoryValue base C z := by
  by_cases hw : lowerWidth (base.2 ++ words.2) ≤ lowerWidth (base.1 ++ words.1)
  · let norm : CertBound := ⟨false,false,lowerHistoryWH words⟩
    have hnorm : lowerHistoryAtBase base [norm] := lowerHistory_normal_left hwidth base words hw
    by_cases hv : upper = !(lowerHistoryWordParity C words false)
    · let vwords := lowerHistorySet words false (lowerHistoryPick words false ++ [1])
      have hpv : lowerHistoryWordParity C vwords false =
          lowerHistoryWordParity C vwords true :=
        lowerHistory_virtual_one_parity_mixed C words false hp
      obtain ⟨z, cs, hzmem, hcs, hzval⟩ := hequal base C hc vwords upper hpv
      have hzmem' : (z,cs) ∈ lowerHistoryEqualCases C vwords upper := by
        simpa only [lowerHistoryEndpointCases, if_pos hpv] using hzmem
      refine ⟨z, norm :: cs, ?_, ?_, ?_⟩
      · unfold lowerHistoryEndpointCases
        rw [if_neg hp]
        simp [lowerHistoryNormalCases, hv, norm, vwords, hzmem']
        rw [hv] at hzmem'
        simpa only [vwords] using hzmem'
      · simp only [lowerHistoryAtBase, lowerHistoryConditions] at hnorm hcs ⊢
        intro b hb
        simp only [List.mem_cons] at hb
        rcases hb with (rfl | hb)
        · exact hnorm _ (by simp)
        · exact hcs b hb
      · exact (lowerHistory_virtual_endpoint_eq base C hc words upper false hp hw hv).trans hzval
    · let z := (lowerHistoryEndVal C words upper false
          (lowerHistoryNatural C words upper false),
        lowerHistoryEndVal C words upper true
          (lowerHistoryNatural C words upper true))
      refine ⟨z, [norm], ?_, hnorm, ?_⟩
      · unfold lowerHistoryEndpointCases
        rw [if_neg hp]
        simp [lowerHistoryNormalCases, hv, norm, z]
      · exact lowerHistory_natural_endpoint_value hcf base C hc words upper false hp hw hv
  · let norm : CertBound := ⟨true,true,lowerHistoryWH words⟩
    have hnorm : lowerHistoryAtBase base [norm] := lowerHistory_normal_right hwidth base words hw
    by_cases hv : upper = !(lowerHistoryWordParity C words true)
    · let vwords := lowerHistorySet words true (lowerHistoryPick words true ++ [1])
      have hpv : lowerHistoryWordParity C vwords false =
          lowerHistoryWordParity C vwords true :=
        lowerHistory_virtual_one_parity_mixed C words true hp
      obtain ⟨z, cs, hzmem, hcs, hzval⟩ := hequal base C hc vwords upper hpv
      have hzmem' : (z,cs) ∈ lowerHistoryEqualCases C vwords upper := by
        simpa only [lowerHistoryEndpointCases, if_pos hpv] using hzmem
      refine ⟨z, norm :: cs, ?_, ?_, ?_⟩
      · unfold lowerHistoryEndpointCases
        rw [if_neg hp]
        simp [lowerHistoryNormalCases, hv, norm, vwords, hzmem']
        rw [hv] at hzmem'
        simpa only [vwords] using hzmem'
      · simp only [lowerHistoryAtBase, lowerHistoryConditions] at hnorm hcs ⊢
        intro b hb
        simp only [List.mem_cons] at hb
        rcases hb with (rfl | hb)
        · exact hnorm _ (by simp)
        · exact hcs b hb
      · exact (lowerHistory_virtual_endpoint_eq base C hc words upper true hp hw hv).trans hzval
    · let z := (lowerHistoryEndVal C words upper false
          (lowerHistoryNatural C words upper false),
        lowerHistoryEndVal C words upper true
          (lowerHistoryNatural C words upper true))
      refine ⟨z, [norm], ?_, hnorm, ?_⟩
      · unfold lowerHistoryEndpointCases
        rw [if_neg hp]
        simp [lowerHistoryNormalCases, hv, norm, z]
      · exact lowerHistory_natural_endpoint_value hcf base C hc words upper true hp hw hv

private theorem mixed_endpoint_cases_core
    (hwidth : LowerHistoryWidthLaw)
    (hcf : ∀ (w : List ℕ+) (z : CertField), 0 ≤ certFieldVal z →
      certFieldVal (lowerHistoryCF w z) = prefixEval w (certFieldVal z))
    (base : LowerPair) (C : LowerHistoryContext) (hc : lowerHistoryContextFits base C)
    (words : LowerPair) (upper : Bool)
    (hp : lowerHistoryWordParity C words false ≠ lowerHistoryWordParity C words true) :
    ∃ z cs, (z,cs) ∈ lowerHistoryEndpointCases C words upper ∧
      lowerHistoryAtBase base cs ∧
      lowerHistoryEndpointReal base C words upper = lowerHistoryValue base C z := by
  exact lowerHistory_mixed_endpoint_cases_from_equal
    (lowerHistory_equal_endpoint_cases hwidth hcf) hwidth hcf base C hc words upper hp


end Freiman

private theorem Freiman.lowerHistory_mixed_endpoint_cases (hwidth : LowerHistoryWidthLaw) (hcf : ∀ (w : List ℕ+) (z : CertField), 0 ≤ certFieldVal z → certFieldVal (lowerHistoryCF w z) = prefixEval w (certFieldVal z))
    (base : LowerPair) (C : LowerHistoryContext) (hc : lowerHistoryContextFits base C) (words : LowerPair) (upper : Bool)
    (hp : lowerHistoryWordParity C words false ≠ lowerHistoryWordParity C words true) :
    ∃ z cs, (z,cs) ∈ lowerHistoryEndpointCases C words upper ∧ lowerHistoryAtBase base cs ∧
      lowerHistoryEndpointReal base C words upper = lowerHistoryValue base C z := by
  exact Freiman.mixed_endpoint_cases_core hwidth hcf base C hc words upper hp




open _root_.Freiman

private theorem prefix_nonneg (w : List ℕ+) (z : ℝ) (hz : 0 ≤ z) :
    0 ≤ prefixEval w z := by
  induction w with
  | nil => exact hz
  | cons a w ih => simp only [prefixEval]; positivity

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

private theorem equal_nonneg (C : LowerHistoryContext) (w : LowerPair) (upper incoming : Bool)
    (z : CertField × CertField) (cs : List CertBound)
    (hz : (z,cs) ∈ trunkEqualCases C w upper incoming) :
    0 ≤ certFieldVal z.1 ∧ 0 ≤ certFieldVal z.2 := by
  by_cases hn : (lowerHistoryNatural C w upper false || lowerHistoryNatural C w upper true) = true
  · simp only [trunkEqualCases, hn, ↓reduceIte, List.mem_singleton, Prod.mk.injEq] at hz
    rcases hz with ⟨rfl,rfl⟩
    exact ⟨endval_nonneg _ _ _ _ _,endval_nonneg _ _ _ _ _⟩
  · dsimp only [trunkEqualCases] at hz
    rw [if_neg hn] at hz
    simp only [List.mem_flatMap,List.mem_map] at hz
    obtain ⟨⟨wide,norm⟩,_,shortened,_,heq⟩ := hz
    cases heq
    exact ⟨endval_nonneg _ _ _ _ _,endval_nonneg _ _ _ _ _⟩

private theorem endpoint_nonneg (C : LowerHistoryContext) (w : LowerPair)
    (upper incoming : Bool) (z : CertField × CertField) (cs : List CertBound)
    (hz : (z,cs) ∈ trunkEndpointCases C w upper incoming) :
    0 ≤ certFieldVal z.1 ∧ 0 ≤ certFieldVal z.2 := by
  unfold trunkEndpointCases at hz
  split_ifs at hz with hp
  · exact equal_nonneg C w upper incoming z cs hz
  · simp only [List.mem_flatMap,List.mem_map] at hz
    obtain ⟨⟨wide,norm⟩,_,⟨v,bs⟩,hv,heq⟩ := hz
    cases heq
    split_ifs at hv
    · exact equal_nonneg _ _ _ _ _ _ hv
    · simp only [List.mem_singleton,Prod.mk.injEq] at hv
      rcases hv with ⟨rfl,rfl⟩
      exact ⟨endval_nonneg _ _ _ _ _,endval_nonneg _ _ _ _ _⟩

private theorem endpoint_core (base : LowerPair) (C : LowerHistoryContext)
    (hc : lowerHistoryContextFits base C) (words : LowerPair) (upper : Bool) :
    ∃ z cs, (z,cs) ∈ trunkEndpointCases C words upper false ∧
      lowerHistoryAtBase base cs ∧
      lowerHistoryEndpointReal base C words upper = lowerHistoryValue base C z := by
  by_cases hp : lowerHistoryWordParity C words false = lowerHistoryWordParity C words true
  · have h := Freiman.lowerHistory_equal_endpoint_cases lowerHistory_width_threshold
      lowerHistory_cf_value base C hc words upper hp
    simpa [TrunkParentAdapt.lowerHistoryEndpointCases,
      TrunkParentAdapt.lowerHistoryEqualCases,TrunkParentAdapt.lowerHistoryNormalCases,
      trunkEndpointCases,trunkEqualCases,trunkNormalCases] using h
  · have h := Freiman.lowerHistory_mixed_endpoint_cases lowerHistory_width_threshold
      lowerHistory_cf_value base C hc words upper hp
    simpa [TrunkParentAdapt.lowerHistoryEndpointCases,
      TrunkParentAdapt.lowerHistoryEqualCases,TrunkParentAdapt.lowerHistoryNormalCases,
      trunkEndpointCases,trunkEqualCases,trunkNormalCases] using h



private theorem normalize_wide (p : LowerPair) :
    lowerWidth (lowerNormalize p).2 ≤ lowerWidth (lowerNormalize p).1 := by
  unfold lowerNormalize
  split_ifs with h
  · exact h
  · exact (lt_of_not_ge h).le

private theorem normalize_idem (p : LowerPair) : lowerNormalize (lowerNormalize p) = lowerNormalize p := by
  conv_lhs => rw [lowerNormalize]
  exact if_pos (normalize_wide p)

private theorem normalize_good (p : LowerPair) (h : lowerGood p) : lowerGood (lowerNormalize p) := by
  simpa only [lowerGood,lowerChild,normalize_idem] using h

private theorem good_cross (base : LowerPair) (C : LowerHistoryContext)
    (hn : lowerNormalize base = base) (hb : lowerGood base) :
    (lowerHistoryEndpointReal base C ([2],[]) false ≤
      lowerHistoryEndpointReal base C ([1],[]) true) ∧
    (lowerHistoryEndpointReal base C ([1],[]) false ≤
      lowerHistoryEndpointReal base C ([2],[]) true) := by
  rcases hb with ⟨x,hx1,hx2⟩
  have h1 : lowerEndpoint (lowerHistoryAppend base ([1],[])) false ≤ x ∧
      x ≤ lowerEndpoint (lowerHistoryAppend base ([1],[])) true := by
    simpa only [lowerCover,Set.mem_Icc,lowerChild,hn,List.reverse_cons,List.reverse_nil,
      List.nil_append,lowerHistoryAppend] using hx1
  have h2 : lowerEndpoint (lowerHistoryAppend base ([2],[])) false ≤ x ∧
      x ≤ lowerEndpoint (lowerHistoryAppend base ([2],[])) true := by
    simpa only [lowerCover,Set.mem_Icc,lowerChild,hn,List.reverse_cons,List.reverse_nil,
      List.nil_append,lowerHistoryAppend] using hx2
  have h21 := h2.1.trans h1.2
  have h12 := h1.1.trans h2.2
  cases ho : lowerHistoryCommonOdd base C <;>
    simp only [lowerHistoryEndpointReal,ho,Bool.false_eq_true,↓reduceIte,
      Bool.xor_false,Bool.xor_true,Bool.not_false,Bool.not_true,one_mul,neg_one_mul]
  · exact ⟨h21,h12⟩
  · exact ⟨neg_le_neg h12,neg_le_neg h21⟩

private theorem hn_holds (base : LowerPair) (hn : lowerNormalize base = base) :
    lowerHistoryAtBase base [lowerHistoryHN] := by
  have hw : lowerWidth base.2 ≤ lowerWidth base.1 := by
    rw [← hn]
    exact normalize_wide base
  simpa [lowerHistoryHN] using
    (lowerHistory_width_threshold base ([],[])).1.mp (by simpa using hw)

private theorem cd_snd_pos (w : List ℕ+) : 0 < ((lowerCD w).2 : ℝ) := by
  have aux : ∀ (v : List ℕ+) (z : ℕ × ℕ), 0 ≤ z.1 → 0 < z.2 →
      0 < (v.foldl (fun z a => (z.2,z.1 + (a : ℕ) * z.2)) z).2 := by
    intro v
    induction v with
    | nil => intro z hz1 hz2; exact_mod_cast hz2
    | cons a v ih =>
        intro z hz1 hz2
        apply ih
        · omega
        · have ha : 0 < (a : ℕ) := PNat.pos a
          exact Nat.add_pos_right _ (Nat.mul_pos ha hz2)
  have hn : 0 < (lowerCD w).2 := by
    exact aux w (0,1) (by omega) (by omega)
  exact_mod_cast hn

private theorem zero_holds (base : LowerPair) : lowerHistoryAtBase base [lowerHistoryZero] := by
  have hq1 := cd_snd_pos base.1
  have hq2 := cd_snd_pos base.2
  have hs : 0 < lowerScale base := by unfold lowerScale; positivity
  simpa [lowerHistoryAtBase,lowerHistoryConditions,lowerHistoryZero,
    lowerHistoryThreshold,lowerHistorySort,lowerHistoryLex,lowerHistoryRat,
    certBoundHolds,certThresholdVal,certThresholdNum,certThresholdDen,certFieldVal] using hs

private def rawParents (C : LowerHistoryContext) : List (List CertBound) :=
  let a := trunkBranches C ⟨([2],[]),true,([1],[]),false,false,[]⟩
  let b := trunkBranches C ⟨([1],[]),true,([2],[]),false,false,[]⟩
  a.flatMap fun (ca,ga) => b.filterMap fun (cb,gb) =>
    let base := ca++cb++[lowerHistoryHN,lowerHistoryZero]
    match ga,gb with
    | .impossible,_ | _,.impossible => none
    | .automatic,.automatic => some base
    | .bound g,.automatic | .automatic,.bound g => some (g::base)
    | .bound g,.bound h => some (g::h::base)

private theorem fold_preserves {α : Type} [DecidableEq α]
    (step : List α → α → List α) (hstep : ∀ acc x, ∀ y ∈ acc, y ∈ step acc x)
    (xs acc : List α) {y : α} (hy : y ∈ acc) : y ∈ xs.foldl step acc := by
  induction xs generalizing acc with
  | nil => exact hy
  | cons x xs ih => exact ih (step acc x) (hstep acc x y hy)

private theorem dedup_rep (raw : List (List CertBound)) (bs : List CertBound)
    (hm : bs ∈ raw) :
    ∃ cs ∈ raw.foldl (fun acc bs =>
      if acc.any (fun ds => decide (ds.toFinset = bs.toFinset)) then acc else acc++[bs]) [],
      cs.toFinset = bs.toFinset := by
  let step := fun acc (x : List CertBound) =>
    if acc.any (fun ds => decide (ds.toFinset = x.toFinset)) then acc else acc++[x]
  have aux : ∀ (xs acc : List (List CertBound)) (target : List CertBound),
      ((∃ cs ∈ acc, cs.toFinset = target.toFinset) ∨ target ∈ xs) →
      ∃ cs ∈ xs.foldl step acc, cs.toFinset = target.toFinset := by
    intro xs
    induction xs with
    | nil =>
        intro acc target h
        rcases h with h | h
        · simpa using h
        · simp at h
    | cons x xs ih =>
        intro acc target h
        apply ih (step acc x) target
        rcases h with hrep | hmem
        · left
          rcases hrep with ⟨cs,hcs,heq⟩
          exact ⟨cs, by
            unfold step
            split <;> simp_all, heq⟩
        · simp only [List.mem_cons] at hmem
          rcases hmem with rfl | htail
          · left
            unfold step
            split_ifs with hex
            · have ha := List.any_eq_true.mp hex
              rcases ha with ⟨cs,hcs,hdec⟩
              exact ⟨cs,hcs,of_decide_eq_true hdec⟩
            · exact ⟨target,by simp,rfl⟩
          · exact Or.inr htail
  exact aux raw [] bs (Or.inr hm)


private theorem append_holds (base : LowerPair) {as bs : List CertBound}
    (ha : lowerHistoryAtBase base as) (hb : lowerHistoryAtBase base bs) :
    lowerHistoryAtBase base (as ++ bs) := by
  intro b hm
  rcases List.mem_append.mp hm with hm | hm
  · exact ha b hm
  · exact hb b hm

private theorem comparison_cons (base : LowerPair) (g : LowerHistoryComparison)
    (hg : lowerHistoryComparisonHolds g (lowerRatio base.1) (lowerRatio base.2) (lowerScale base))
    (bs : List CertBound) (hbs : lowerHistoryAtBase base bs) :
    lowerHistoryAtBase base (match g with | .bound b => b :: bs | _ => bs) := by
  cases g with
  | automatic => exact hbs
  | impossible => exact hg.elim
  | bound b =>
      intro c hc
      simp only [List.mem_cons] at hc
      rcases hc with rfl | hc
      · simpa [lowerHistoryComparisonHolds] using hg
      · exact hbs c hc

private theorem trunkGreater_false (C : LowerHistoryContext)
    (x y : CertField × CertField) :
    trunkGreater C x y false = lowerHistoryGreater C x y := by
  unfold trunkGreater lowerHistoryGreater
  dsimp
  split_ifs <;> rfl

private theorem collect_parent (base : LowerPair) (C : LowerHistoryContext)
    (hc : lowerHistoryContextFits base C) (hn : lowerNormalize base = base)
    (hgood : lowerGood base) :
    ∃ bs ∈ rawParents C, lowerHistoryAtBase base bs := by
  obtain ⟨xa,cxa,hxam,hxac,hxav⟩ := endpoint_core base C hc ([2],[]) true
  obtain ⟨ya,cya,hyam,hyac,hyav⟩ := endpoint_core base C hc ([1],[]) false
  obtain ⟨xb,cxb,hxbm,hxbc,hxbv⟩ := endpoint_core base C hc ([1],[]) true
  obtain ⟨yb,cyb,hybm,hybc,hybv⟩ := endpoint_core base C hc ([2],[]) false
  have hcross := good_cross base C hn hgood
  have hga : lowerHistoryComparisonHolds (trunkGreater C xa ya false)
      (lowerRatio base.1) (lowerRatio base.2) (lowerScale base) := by
    rw [trunkGreater_false]
    apply (lowerHistory_greater_from_sign lowerHistory_sign_value base C hc xa ya
      (endpoint_nonneg _ _ _ _ _ _ hxam) (endpoint_nonneg _ _ _ _ _ _ hyam)).mpr
    rw [← hxav,← hyav]
    exact hcross.2
  have hgb : lowerHistoryComparisonHolds (trunkGreater C xb yb false)
      (lowerRatio base.1) (lowerRatio base.2) (lowerScale base) := by
    rw [trunkGreater_false]
    apply (lowerHistory_greater_from_sign lowerHistory_sign_value base C hc xb yb
      (endpoint_nonneg _ _ _ _ _ _ hxbm) (endpoint_nonneg _ _ _ _ _ _ hybm)).mpr
    rw [← hxbv,← hybv]
    exact hcross.1
  have ha : (cxa ++ cya,trunkGreater C xa ya false) ∈
      trunkBranches C ⟨([2],[]),true,([1],[]),false,false,[]⟩ := by
    unfold trunkBranches
    exact List.mem_flatMap.mpr ⟨(xa,cxa),hxam,
      List.mem_map.mpr ⟨(ya,cya),hyam,by simp [trunkSpecIncoming]⟩⟩
  have hb : (cxb ++ cyb,trunkGreater C xb yb false) ∈
      trunkBranches C ⟨([1],[]),true,([2],[]),false,false,[]⟩ := by
    unfold trunkBranches
    exact List.mem_flatMap.mpr ⟨(xb,cxb),hxbm,
      List.mem_map.mpr ⟨(yb,cyb),hybm,by simp [trunkSpecIncoming]⟩⟩
  let ca := cxa ++ cya
  let cb := cxb ++ cyb
  let cuts := ca ++ cb ++ [lowerHistoryHN,lowerHistoryZero]
  have htail : lowerHistoryAtBase base [lowerHistoryHN,lowerHistoryZero] := by
    intro b hm
    simp only [List.mem_cons, List.mem_singleton] at hm
    rcases hm with h | h
    · subst b
      exact hn_holds base hn lowerHistoryHN (by simp)
    · rcases h with rfl | h
      · exact zero_holds base lowerHistoryZero (by simp)
      · simp at h
  have hcuts : lowerHistoryAtBase base cuts := by
    exact append_holds base
      (append_holds base (append_holds base hxac hyac)
        (append_holds base hxbc hybc)) htail
  generalize ega : trunkGreater C xa ya false = ga at hga ha
  generalize egb : trunkGreater C xb yb false = gb at hgb hb
  cases ga with
  | impossible => exact hga.elim
  | automatic =>
      cases gb with
      | impossible => exact hgb.elim
      | automatic =>
          refine ⟨cuts,?_,hcuts⟩
          unfold rawParents
          exact List.mem_flatMap.mpr ⟨(ca,.automatic),by simpa [ca] using ha,
            List.mem_filterMap.mpr ⟨(cb,.automatic),by simpa [cb] using hb,
              by simp [cuts, ca, cb]⟩⟩
      | bound g =>
          refine ⟨g::cuts,?_,comparison_cons base (.bound g) hgb _ hcuts⟩
          unfold rawParents
          exact List.mem_flatMap.mpr ⟨(ca,.automatic),by simpa [ca] using ha,
            List.mem_filterMap.mpr ⟨(cb,.bound g),by simpa [cb] using hb,
              by simp [cuts, ca, cb]⟩⟩
  | bound g =>
      cases gb with
      | impossible => exact hgb.elim
      | automatic =>
          refine ⟨g::cuts,?_,comparison_cons base (.bound g) hga _ hcuts⟩
          unfold rawParents
          exact List.mem_flatMap.mpr ⟨(ca,.bound g),by simpa [ca] using ha,
            List.mem_filterMap.mpr ⟨(cb,.automatic),by simpa [cb] using hb,
              by simp [cuts, ca, cb]⟩⟩
      | bound h =>
          refine ⟨g::h::cuts,?_,comparison_cons base (.bound g) hga _
            (comparison_cons base (.bound h) hgb _ hcuts)⟩
          unfold rawParents
          exact List.mem_flatMap.mpr ⟨(ca,.bound g),by simpa [ca] using ha,
            List.mem_filterMap.mpr ⟨(cb,.bound h),by simpa [cb] using hb,
              by simp [cuts, ca, cb]⟩⟩

end TrunkParentAdapt

open Freiman

private theorem parent_mode_core (t : ℝ) (p : LowerPair) (hs : lowerState t p) (k : Fin 16)
    (hf : lowerHistoryContextFits (lowerNormalize p) (trunkCatalog.states k).context) :
    ∃ par : ℕ, par < (trunkParents (trunkCatalog.states k).context).length ∧
    trunkHolds ((trunkParents (trunkCatalog.states k).context)[par]?.getD [])
      (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2)
      (lowerScale (lowerNormalize p)) := by
  let base := lowerNormalize p
  let C := (trunkCatalog.states k).context
  have hn : lowerNormalize base = base := by
    simpa [base] using TrunkParentAdapt.normalize_idem p
  have hg : lowerGood base := by
    exact TrunkParentAdapt.normalize_good p hs.2.1
  obtain ⟨bs,hraw,hholds⟩ := TrunkParentAdapt.collect_parent base C hf hn hg
  obtain ⟨cs,hfold,hfin⟩ := TrunkParentAdapt.dedup_rep
    (TrunkParentAdapt.rawParents C) bs hraw
  have hmem : cs ∈ trunkParents C := by
    change cs ∈ (TrunkParentAdapt.rawParents C).foldl
      (fun acc bs => if acc.any (fun ds => decide (ds.toFinset = bs.toFinset))
        then acc else acc ++ [bs]) []
    exact hfold
  have hcsholds : lowerHistoryAtBase base cs := by
    intro b hb
    apply hholds b
    have hm : b ∈ cs.toFinset := by simpa using hb
    rw [hfin] at hm
    simpa using hm
  obtain ⟨par,hpar⟩ := List.mem_iff_getElem?.mp hmem
  have hlt : par < (trunkParents C).length := by
    by_contra hnot
    have hnone := List.getElem?_eq_none (l := trunkParents C) (i := par)
      (Nat.le_of_not_gt hnot)
    rw [hnone] at hpar
    contradiction
  refine ⟨par,hlt,?_⟩
  simpa [C, base, hpar, trunkHolds, lowerHistoryAtBase,
    lowerHistoryConditions] using hcsholds


theorem solution (t : ℝ) (p : LowerPair) (hs : lowerState t p) (k : Fin 16)
    (hf : lowerHistoryContextFits (lowerNormalize p) (trunkCatalog.states k).context) :
    ∃ par : ℕ, par < (trunkParents (trunkCatalog.states k).context).length ∧
    trunkHolds ((trunkParents (trunkCatalog.states k).context)[par]?.getD [])
      (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2) (lowerScale (lowerNormalize p)) := by
  exact parent_mode_core t p hs k hf

#print axioms solution
