-- Prove2me | solution 1 for Freiman.lower_h5_numeric_to_anchor
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-13T08:28:05.464508+00:00
-- url     : https://prove2.me/submissions/a99b94d8-f296-48ee-8c71-128a1a8a6044

import Definitions.Def_Freiman_lowerHistoryVerification
import Theorems.Thm_Freiman_lowerHistory_cf_value
import Theorems.Thm_Freiman_lowerHistory_sign_value
import Mathlib.Tactic
import Definitions.Def_Freiman_lowerH5Verification
import Theorems.Thm_Freiman_lower_forced_reflections
import Theorems.Thm_Freiman_lowerEarlyTerminal_endpoint_swap_nontie


open Freiman
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

private theorem field_sub (x y : CertField) :
    certFieldVal (certFieldSub x y) = certFieldVal x - certFieldVal y := by
  simp only [certFieldVal, certFieldSub]
  push_cast
  ring

private theorem sign_nonneg (z : CertField) (b : Bool) :
    (0 ≤ (if b then -1 else 1 : ℤ) * lowerHistorySign z) ↔
      (0 ≤ (if b then -1 else 1 : ℝ) * certFieldVal z) := by
  have hsg := lowerHistory_sign_value z
  have hle : lowerHistorySign z ≤ 0 ↔ certFieldVal z ≤ 0 := by
    simpa only [not_lt] using not_congr hsg.2
  have hlt : lowerHistorySign z < 0 ↔ certFieldVal z < 0 := by
    simp only [lt_iff_le_and_ne, hle, ne_eq, hsg.1]
  have hge : 0 ≤ lowerHistorySign z ↔ 0 ≤ certFieldVal z := by
    simpa only [not_lt] using not_congr hlt
  cases b
  · simpa using hge
  · simpa using hle

private theorem value_mono (hg : LowerHistoryGreaterLaw) (base : LowerPair)
    (C : LowerHistoryContext) (hc : lowerHistoryContextFits base C)
    (x y : CertField × CertField)
    (hx : 0 ≤ certFieldVal x.1 ∧ 0 ≤ certFieldVal x.2)
    (hy : 0 ≤ certFieldVal y.1 ∧ 0 ≤ certFieldVal y.2)
    (h1 : 0 ≤ (if C.parity.1 then -1 else 1 : ℝ) *
      (certFieldVal x.1 - certFieldVal y.1))
    (h2 : 0 ≤ (if C.parity.2 then -1 else 1 : ℝ) *
      (certFieldVal x.2 - certFieldVal y.2)) :
    lowerHistoryValue base C y ≤ lowerHistoryValue base C x := by
  have hs1 : 0 ≤ (if C.parity.1 then -1 else 1 : ℤ) *
      lowerHistorySign (certFieldSub x.1 y.1) :=
    (sign_nonneg _ _).mpr (by simpa only [field_sub] using h1)
  have hs2 : 0 ≤ (if C.parity.2 then -1 else 1 : ℤ) *
      lowerHistorySign (certFieldSub x.2 y.2) :=
    (sign_nonneg _ _).mpr (by simpa only [field_sub] using h2)
  apply (hg base C hc x y hx hy).mp
  simp only [lowerHistoryGreater, hs1, hs2, and_self, ↓reduceIte,
    lowerHistoryComparisonHolds]

end M7Goodness14


open Freiman
namespace M7H5Numeric14

private theorem numeric_compare (he : LowerHistoryEndpointLaw) (hg : LowerHistoryGreaterLaw)
    (c : LowerH5Case) (base : LowerPair) (hfit : lowerHistoryContextFits base c.context)
    (hr : certRectangleMem c.rectangle (lowerRatio base.1) (lowerRatio base.2))
    (hb : lowerHistoryAtBase base (lowerH5Premises c)) (hn : lowerH5Numeric c) :
    lowerHistoryEndpointReal base c.context (lowerH5GoalWords c) false ≤
      lowerHistoryEndpointReal base c.context c.words false ∨ lowerH5Exceptional c := by
  obtain ⟨x,cx,hx,hcx,hex⟩ := he base c.context hfit c.words false
  obtain ⟨y,cy,hy,hcy,hey⟩ := he base c.context hfit (lowerH5GoalWords c) false
  have hm : (cx++cy,lowerHistoryGreater c.context x y) ∈ lowerH5Comparisons c := by
    unfold lowerH5Comparisons lowerHistoryComparisons
    exact List.mem_flatMap.mpr ⟨(x,cx),hx,List.mem_map.mpr ⟨(y,cy),hy,rfl⟩⟩
  obtain ⟨bi,hbi⟩ := List.mem_iff_getElem?.mp hm
  have hconds : lowerHistoryAtBase base (cx++cy) := by
    intro b hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact hcx b hmem
    · exact hcy b hmem
  rcases hn _ _ _ hr hb bi _ _ hbi hconds with hc | hexc
  · left
    rw [hex,hey]
    exact (hg base c.context hfit x y
      (M7Goodness14.endpoint_nonneg _ _ _ _ _ hx)
      (M7Goodness14.endpoint_nonneg _ _ _ _ _ hy)).mp hc
  · exact Or.inr hexc.1

private theorem normal_odd (base : LowerPair) (c : LowerH5Case)
    (hc : lowerHistoryContextFits base c.context) (hs : lowerH5CaseShape c) :
    decide ((lowerHistoryOrient (lowerHistoryAppend base c.words) c.reflect).1.length % 2 = 1) =
      lowerHistoryCommonOdd base c.context := by
  have hw := hs.1
  have hp := hs.2.1
  have hr := hs.2.2.1
  have hfit := hc.2.2
  rcases Nat.mod_two_eq_zero_or_one base.1.length with h1 | h1 <;>
    rcases Nat.mod_two_eq_zero_or_one base.2.length with h2 | h2 <;>
    cases hk : c.kind <;>
    simp_all [lowerH5ExpectedWords, lowerH5ExpectedParity, lowerHistoryOrient,
      lowerHistoryAppend, lowerHistoryCommonOdd, List.length_append, Nat.add_mod]

private theorem child_equal_parity (p : LowerPair) (hm : lowerMixed p) :
    (lowerChild p ([2],[])).1.length % 2 = (lowerChild p ([2],[])).2.length % 2 := by
  have hn : (lowerNormalize p).1.length % 2 ≠ (lowerNormalize p).2.length % 2 := by
    unfold lowerNormalize
    split_ifs
    · exact hm
    · exact Ne.symm hm
  simp only [lowerChild, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.length_append, List.length_cons, List.length_nil]
  omega

private theorem child_swap (p : LowerPair) (hm : lowerMixed p)
    (hg : lowerGood p) (hb : lowerParameterBox p) (upper : Bool) :
    lowerEndpoint (lowerChild p ([2],[])) upper =
      lowerEndpoint ((lowerChild p ([2],[])).2,(lowerChild p ([2],[])).1) upper := by
  apply lowerEarlyTerminal_endpoint_swap_nontie
  constructor
  · have hw := (lower_forced_reflections p hg hb).1
    exact ne_of_lt (by simpa [lowerChild] using hw)
  · intro h
    exact (h (child_equal_parity p hm)).elim

private theorem goal_pair (base : LowerPair) (c : LowerH5Case)
    (hn : lowerNormalize (lowerHistoryAppend base c.words) =
      lowerHistoryOrient (lowerHistoryAppend base c.words) c.reflect) :
    lowerHistoryAppend base (lowerH5GoalWords c) =
      lowerHistoryOrient (lowerChild (lowerHistoryAppend base c.words) ([2],[])) c.reflect := by
  unfold lowerChild
  rw [hn]
  cases hr : c.reflect <;>
    simp [lowerH5GoalWords, hr, lowerHistoryOrient,
      lowerHistoryAppend, List.append_assoc]

private theorem even_iff (n : ℕ) (b : Bool) (h : decide (n % 2 = 1) = b) :
    n % 2 = 0 ↔ b = false := by
  subst b
  by_cases h0 : n % 2 = 0
  · have h1 : ¬ n % 2 = 1 := by omega
    simp [h0,h1]
  · have h1 : n % 2 = 1 := by omega
    simp [h0,h1]

private theorem local_goal (base : LowerPair) (c : LowerH5Case) (t : ℝ)
    (hfit : lowerHistoryContextFits base c.context) (hshape : lowerH5CaseShape c)
    (hn : lowerNormalize (lowerHistoryAppend base c.words) =
      lowerHistoryOrient (lowerHistoryAppend base c.words) c.reflect)
    (hm : lowerMixed (lowerHistoryAppend base c.words))
    (hg : lowerGood (lowerHistoryAppend base c.words))
    (hb : lowerParameterBox (lowerHistoryAppend base c.words)) :
    lowerLocalLower (lowerHistoryAppend base c.words) ([2],[]) =
      lowerHistoryEndpointReal base c.context (lowerH5GoalWords c) false ∧
    lowerLocalCoordinate (lowerHistoryAppend base c.words) t =
      (if lowerHistoryCommonOdd base c.context then -1 else 1 : ℝ)*t := by
  have ho := normal_odd base c hfit hshape
  rw [←hn] at ho
  have heven := even_iff _ _ ho
  have he (upper : Bool) :
      lowerEndpoint (lowerHistoryAppend base (lowerH5GoalWords c)) upper =
        lowerEndpoint (lowerChild (lowerHistoryAppend base c.words) ([2],[])) upper := by
    rw [goal_pair base c hn]
    cases hr : c.reflect
    · rfl
    · exact (child_swap _ hm hg hb upper).symm
  constructor <;> cases hob : lowerHistoryCommonOdd base c.context <;>
    simp [lowerLocalLower, lowerLocalCoordinate, lowerHistoryEndpointReal, heven, hob, he]

private theorem parent_lower (base : LowerPair) (c : LowerH5Case) (t : ℝ)
    (ht : t ∈ lowerCover (lowerHistoryAppend base c.words)) :
    lowerHistoryEndpointReal base c.context c.words false ≤
      (if lowerHistoryCommonOdd base c.context then -1 else 1 : ℝ)*t := by
  cases ho : lowerHistoryCommonOdd base c.context <;>
    simp only [lowerHistoryEndpointReal, ho, Bool.false_eq_true, ↓reduceIte,
      Bool.false_xor, one_mul, neg_one_mul]
  · exact ht.1
  · exact neg_le_neg ht.2

private theorem numeric_to_anchor (he : LowerHistoryEndpointLaw) (hg : LowerHistoryGreaterLaw)
    (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n)
    (ha : lowerH5Active (h n)) (c : LowerH5Case) (hshape : lowerH5CaseShape c)
    (hc : lowerH5Immediate h n c) (hs : lowerH5ReachedPremises h n c)
    (hn : lowerH5Numeric c) : lowerH5LowerBound (h n) t ∨ lowerH5Exceptional c := by
  obtain ⟨m,hm,hfit,happ,horient,_⟩ := hc
  obtain ⟨m',hm',hr,hprem⟩ := hs
  have heq : m' = m := by omega
  subst m'
  rcases numeric_compare he hg c (lowerNormalize (h m)) hfit hr hprem hn with hnum | hexc
  · left
    have hstate := hh.2.1 n le_rfl
    rw [happ] at hstate ha horient ⊢
    have hloc := local_goal (lowerNormalize (h m)) c t hfit hshape horient
      ha.1 hstate.2.1 hstate.2.2.2
    unfold lowerH5LowerBound
    rw [hloc.1,hloc.2]
    exact hnum.trans (parent_lower _ c t hstate.2.2.1)
  · exact Or.inr hexc

end M7H5Numeric14

theorem solution (he : LowerHistoryEndpointLaw) (hg : LowerHistoryGreaterLaw)
    (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n)
    (ha : lowerH5Active (h n)) (c : LowerH5Case) (hshape : lowerH5CaseShape c)
    (hc : lowerH5Immediate h n c) (hs : lowerH5ReachedPremises h n c)
    (hn : lowerH5Numeric c) : lowerH5LowerBound (h n) t ∨ lowerH5Exceptional c := by
  exact M7H5Numeric14.numeric_to_anchor he hg t h n hh ha c hshape hc hs hn

#print axioms solution
