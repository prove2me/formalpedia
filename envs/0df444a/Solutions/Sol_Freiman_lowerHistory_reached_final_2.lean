-- Prove2me | solution 2 for Freiman.lowerHistory_reached_final
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-13T13:00:45.173001+00:00
-- url     : https://prove2.me/submissions/cf328eb4-4f23-4f36-925b-3c77fcbe748d

import Definitions.Def_Freiman_lowerHistoryVerification
import Theorems.Thm_Freiman_lowerHistory_cf_value
import Theorems.Thm_Freiman_lowerHistory_sign_value
import Mathlib.Tactic
import Theorems.Thm_Freiman_lowerHistory_width_threshold
import Theorems.Thm_Freiman_lowerHistory_theta_values


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

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Transfer15

private theorem rawStep_append (base words : LowerPair) (wide : Bool) (l : LowerLabel) :
    lowerHistoryRawStep (lowerHistoryAppend base words) wide l =
      lowerHistoryAppend base (lowerHistoryRawStep words wide l) := by
  cases wide <;> simp [lowerHistoryRawStep, lowerHistoryAppend, List.append_assoc]

private theorem fold_append (base : LowerPair) :
    ∀ (xs : List (LowerLabel × Bool)) (r : LowerPair × Bool),
      List.foldl (fun s step => (lowerHistoryRawStep s.1 s.2 step.1,
        if step.2 then !s.2 else s.2))
          (lowerHistoryAppend base r.1, r.2) xs =
      let z := List.foldl (fun s step => (lowerHistoryRawStep s.1 s.2 step.1,
        if step.2 then !s.2 else s.2)) r xs
      (lowerHistoryAppend base z.1, z.2) := by
  intro xs
  induction xs with
  | nil => intro r; rfl
  | cons step tail ih =>
      intro r
      simp only [List.foldl_cons]
      rw [rawStep_append]
      simpa using ih (lowerHistoryRawStep r.1 r.2 step.1,
        if step.2 then !r.2 else r.2)

private theorem replay_append (base : LowerPair) (p : LowerHistoryPath) (j : ℕ) :
    (lowerHistoryReplay base p j).1 =
      lowerHistoryAppend base (lowerHistoryReplay ([],[]) p j).1 ∧
    (lowerHistoryReplay base p j).2 = (lowerHistoryReplay ([],[]) p j).2 := by
  unfold lowerHistoryReplay
  have hi : lowerHistoryRawStep base false p.entry =
      lowerHistoryAppend base (lowerHistoryRawStep ([],[]) false p.entry) := by
    simpa [lowerHistoryAppend] using rawStep_append base ([],[]) false p.entry
  rw [hi]
  have hf := fold_append base (p.steps.take j)
    (lowerHistoryRawStep ([],[]) false p.entry, p.initialWider)
  exact ⟨by simpa using congrArg Prod.fst hf, by simpa using congrArg Prod.snd hf⟩

private theorem decide_add_odd (m n : ℕ) :
    decide ((m+n) % 2 = 1) =
      (decide (m % 2 = 1)).xor (decide (n % 2 = 1)) := by
  rcases Nat.mod_two_eq_zero_or_one m with hm | hm <;>
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn <;>
    simp [Nat.add_mod, hm, hn]

private theorem even_of_decide_not_odd (n : ℕ) (h : decide (n % 2 = 1) = false) :
    n % 2 = 0 := by
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn
  · exact hn
  · simp [hn] at h

private theorem advance_shape (r : LowerPair × Bool) (s : LowerHistoryState)
    (l : LowerLabel) (reflect : Bool)
    (hshape : s.context.parity =
        (decide (r.1.1.length % 2 = 1), decide (r.1.2.length % 2 = 1)) ∧
      s.wider = r.2) :
    let r' := (lowerHistoryRawStep r.1 r.2 l, if reflect then !r.2 else r.2)
    let s' := lowerHistoryAdvance s l reflect
    s'.context.parity =
        (decide (r'.1.1.length % 2 = 1), decide (r'.1.2.length % 2 = 1)) ∧
      s'.wider = r'.2 := by
  rcases r with ⟨words,wide⟩
  rcases s with ⟨C,swide,marked,previous⟩
  simp only at hshape ⊢
  unfold lowerHistoryAdvance
  dsimp only
  rw [hshape.1, hshape.2]
  cases wide <;> cases reflect <;>
    simp [lowerHistoryAdvance, lowerHistoryRawStep, List.length_append,
      decide_add_odd, Bool.xor_comm]

private theorem fold_shape :
    ∀ (xs : List (LowerLabel × Bool)) (r : LowerPair × Bool) (s : LowerHistoryState),
      (s.context.parity =
          (decide (r.1.1.length % 2 = 1), decide (r.1.2.length % 2 = 1)) ∧
        s.wider = r.2) →
      let rr := List.foldl (fun z step => (lowerHistoryRawStep z.1 z.2 step.1,
        if step.2 then !z.2 else z.2)) r xs
      let ss := xs.foldl (fun z step => lowerHistoryAdvance z step.1 step.2) s
      ss.context.parity =
          (decide (rr.1.1.length % 2 = 1), decide (rr.1.2.length % 2 = 1)) ∧
        ss.wider = rr.2 := by
  intro xs
  induction xs with
  | nil => intro r s hs; exact hs
  | cons step tail ih =>
      intro r s hs
      simp only [List.foldl_cons]
      rcases step with ⟨l,reflect⟩
      apply ih
      exact advance_shape r s l reflect hs

private theorem state_replay_shape (p : LowerHistoryPath) (j : ℕ) :
    let r := lowerHistoryReplay ([],[]) p j
    let s := lowerHistoryStateAt p j
    s.context.parity =
      (decide (r.1.1.length % 2 = 1), decide (r.1.2.length % 2 = 1)) ∧
    s.wider = r.2 := by
  classical
  unfold lowerHistoryReplay lowerHistoryStateAt
  apply fold_shape
  simp [lowerHistoryInitialState, lowerHistoryRawStep]

private theorem endpoint_compare (hg : LowerHistoryGreaterLaw) (he : LowerHistoryEndpointLaw)
    (base : LowerPair) (p : LowerHistoryPath)
    (hfit : lowerHistoryContextFits base ⟨(p.context,[3,1]),(false,false)⟩)
    (hc : lowerHistoryComparisonsHold p (lowerRatio base.1)
      (lowerRatio base.2) (lowerScale base)) :
    let ancestor : LowerPair := if ([3,1] : List ℕ+).IsSuffix p.context then ([],[]) else ([3],[2])
    let upper := decide (¬ ([3,1] : List ℕ+).IsSuffix p.context)
    let w := lowerHistoryFinalWords p
    let goal := (w.1 ++ (if p.row = 1 then [1] else [2]),
      w.2 ++ (if p.row = 4 then [1] else [2]))
    lowerHistoryEndpointReal base ⟨(p.context,[3,1]),(false,false)⟩ goal false ≤
      lowerHistoryEndpointReal base ⟨(p.context,[3,1]),(false,false)⟩ ancestor upper := by
  classical
  dsimp only
  let C : LowerHistoryContext := ⟨(p.context,[3,1]),(false,false)⟩
  let ancestor : LowerPair := if ([3,1] : List ℕ+).IsSuffix p.context then ([],[]) else ([3],[2])
  let upper := decide (¬ ([3,1] : List ℕ+).IsSuffix p.context)
  let w := lowerHistoryFinalWords p
  let goal : LowerPair := (w.1 ++ (if p.row = 1 then [1] else [2]),
    w.2 ++ (if p.row = 4 then [1] else [2]))
  obtain ⟨x,cx,hx,hcx,hex⟩ := he base C hfit ancestor upper
  obtain ⟨y,cy,hy,hcy,hey⟩ := he base C hfit goal false
  have hm : (cx++cy,lowerHistoryGreater C x y) ∈ lowerHistoryEndpointComparisons p := by
    unfold lowerHistoryEndpointComparisons lowerHistoryComparisons
    change (cx ++ cy, lowerHistoryGreater C x y) ∈
      (lowerHistoryEndpointCases C ancestor upper).flatMap fun z =>
        (lowerHistoryEndpointCases C goal false).map fun v =>
          (z.2 ++ v.2, lowerHistoryGreater C z.1 v.1)
    exact List.mem_flatMap.mpr ⟨(x,cx),hx,List.mem_map.mpr ⟨(y,cy),hy,rfl⟩⟩
  have hconds : lowerHistoryConditions (cx++cy) (lowerRatio base.1)
      (lowerRatio base.2) (lowerScale base) := by
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact hcx b hb
    · exact hcy b hb
  have hcmp := hc _ hm hconds
  rw [hex, hey]
  exact (hg base C hfit x y
    (M7Goodness14.endpoint_nonneg _ _ _ _ _ hx)
    (M7Goodness14.endpoint_nonneg _ _ _ _ _ hy)).mp hcmp

private theorem reached_context (t : ℝ) (h : ℕ → LowerPair) (n : ℕ)
    (base : LowerPair) (p : LowerHistoryPath) (hr : lowerHistoryReached t h n base p)
    (hi : p.catalog ≠ .initial) :
    lowerHistoryContextFits base ⟨(p.context,[3,1]),(false,false)⟩ := by
  rcases hr with ⟨start, flip, hsum, hreal, hentry⟩
  rw [if_neg hi] at hentry
  unfold lowerHistoryRealizes at hreal
  simp only [hi, if_false] at hreal
  rcases hreal with ⟨hctx, hrctx, hpar, _⟩
  have hnot3 : ¬ lowerEnds base.2 [3] := by
    intro h3
    have h1 := hrctx.1.getLast (by simp)
    have h3' := h3.getLast (by simp)
    have heq : (1 : ℕ+) = 3 := h1.trans h3'.symm
    norm_num at heq
  refine ⟨hctx, ?_, ?_⟩
  · refine ⟨hrctx.1, ?_, ?_⟩
    · refine ⟨fun hb => (hnot3 hb).elim, ?_⟩
      intro hb
      have hz := hb.getLast (by simp)
      norm_num at hz
    · exact ⟨fun _ => by simp [lowerEnds], fun _ => hrctx.1⟩
  · simp only [Bool.xor_false]
    rw [hpar]


end Transfer15



open Freiman
namespace Final15

private theorem threshold_value (c : CertField) (x y : CertField × CertField)
    (r s : ℝ) :
    certThresholdVal (lowerHistoryThreshold c x y) r s =
      certFieldVal c * ((1+s*certFieldVal y.1)*(1+s*certFieldVal y.2)) /
        ((1+r*certFieldVal x.1)*(1+r*certFieldVal x.2)) := by
  simp only [lowerHistoryThreshold,lowerHistorySort]
  split <;> split <;>
    simp only [certThresholdVal,certThresholdNum,certThresholdDen] <;> ring

private theorem threshold_values (p : LowerPair) :
    certThresholdVal lowerHistoryH7.threshold (lowerRatio (lowerNormalize p).1)
      (lowerRatio (lowerNormalize p).2) = lowerThreshold p (31/100) 3 63 25 66 ∧
    certThresholdVal lowerHistoryH9.threshold (lowerRatio (lowerNormalize p).1)
      (lowerRatio (lowerNormalize p).2) = lowerThreshold p ((3-Real.sqrt 3)/2) 36 63 63 66 ∧
    certThresholdVal lowerHistoryH2.threshold (lowerRatio (lowerNormalize p).1)
      (lowerRatio (lowerNormalize p).2) = lowerThreshold p (37/50) 63 70 66 90 ∧
    certThresholdVal lowerHistoryH5.threshold (lowerRatio (lowerNormalize p).1)
      (lowerRatio (lowerNormalize p).2) = lowerThreshold p (279/500) 35 63 63 70 := by
  simp only [lowerHistoryH7,lowerHistoryH9,lowerHistoryH2,lowerHistoryH5,lowerHistoryPB,
    threshold_value,lowerThreshold,lowerHistory_theta_values 3 (by simp),
    lowerHistory_theta_values 63 (by simp),lowerHistory_theta_values 25 (by simp),
    lowerHistory_theta_values 66 (by simp),lowerHistory_theta_values 36 (by simp),
    lowerHistory_theta_values 70 (by simp),lowerHistory_theta_values 90 (by simp),
    lowerHistory_theta_values 35 (by simp)]
  norm_num [lowerHistoryRat,certFieldVal]
  ring

private theorem normal_wide (p : LowerPair) :
    lowerWidth (lowerNormalize p).2 ≤ lowerWidth (lowerNormalize p).1 := by
  unfold lowerNormalize
  split_ifs with hw
  · exact hw
  · exact (not_le.mp hw).le

private theorem final_cuts (q : LowerPair) (row : ℕ) (hh : lowerHistoryHazard row q) :
    lowerHistoryAtBase (lowerNormalize q) (lowerHistoryFinalCuts row) := by
  have hv := threshold_values q
  have hn := (lowerHistory_width_threshold (lowerNormalize q) ([],[])).1.mp
    (by simpa using normal_wide q)
  have hn' : certBoundHolds lowerHistoryHN
      (lowerRatio (lowerNormalize q).1) (lowerRatio (lowerNormalize q).2)
      (lowerScale (lowerNormalize q)) := hn _ (by simp [lowerHistoryHN])
  have h7 : ¬lowerA q 3 ↔ certBoundHolds lowerHistoryH7
      (lowerRatio (lowerNormalize q).1) (lowerRatio (lowerNormalize q).2)
      (lowerScale (lowerNormalize q)) := by
    change ¬(lowerScale (lowerNormalize q) < lowerThreshold q (31/100) 3 63 25 66) ↔
      certThresholdVal lowerHistoryH7.threshold _ _ ≤ lowerScale (lowerNormalize q)
    rw [hv.1]
    exact not_lt
  have h9 : ¬lowerA q 9 ↔ certBoundHolds (lowerHistoryComplement lowerHistoryH9)
      (lowerRatio (lowerNormalize q).1) (lowerRatio (lowerNormalize q).2)
      (lowerScale (lowerNormalize q)) := by
    change ¬(lowerScale (lowerNormalize q) ≤ lowerThreshold q ((3-Real.sqrt 3)/2) 36 63 63 66) ↔
      certThresholdVal lowerHistoryH9.threshold _ _ < lowerScale (lowerNormalize q)
    rw [hv.2.1]
    exact not_le
  have h2 : ¬lowerH q 2 ↔ certBoundHolds (lowerHistoryComplement lowerHistoryH2)
      (lowerRatio (lowerNormalize q).1) (lowerRatio (lowerNormalize q).2)
      (lowerScale (lowerNormalize q)) := by
    change ¬(lowerScale (lowerNormalize q) > lowerThreshold q (37/50) 63 70 66 90) ↔
      lowerScale (lowerNormalize q) ≤ certThresholdVal lowerHistoryH2.threshold _ _
    rw [hv.2.2.1]
    exact not_lt
  have h5 : ¬lowerH q 5 ↔ certBoundHolds (lowerHistoryComplement lowerHistoryH5)
      (lowerRatio (lowerNormalize q).1) (lowerRatio (lowerNormalize q).2)
      (lowerScale (lowerNormalize q)) := by
    change ¬(lowerScale (lowerNormalize q) < lowerThreshold q (279/500) 35 63 63 70) ↔
      certThresholdVal lowerHistoryH5.threshold _ _ ≤ lowerScale (lowerNormalize q)
    rw [hv.2.2.2]
    exact not_lt
  have hrow : row = 1 ∨ row = 2 ∨ row = 3 ∨ row = 4 := by
    by_contra h
    simp only [not_or] at h
    simp [lowerHistoryHazard,h.1,h.2.1,h.2.2.1,h.2.2.2] at hh
  rcases hrow with rfl | rfl | rfl | rfl
  · simpa [lowerHistoryFinalCuts,lowerHistoryAtBase,lowerHistoryConditions] using
      And.intro (h7.mp hh.2.1) (And.intro (h9.mp hh.2.2.1) hn')
  · simpa [lowerHistoryFinalCuts,lowerHistoryAtBase,lowerHistoryConditions] using
      And.intro (h7.mp hh.2.1) hn'
  · simpa [lowerHistoryFinalCuts,lowerHistoryAtBase,lowerHistoryConditions] using
      And.intro (h2.mp hh.2.1) (And.intro (h5.mp hh.2.2.1) hn')
  · simpa [lowerHistoryFinalCuts,lowerHistoryAtBase,lowerHistoryConditions] using
      And.intro (h2.mp hh.2.1) (And.intro (h5.mp hh.2.2.1) hn')

private theorem final_cut_fields (row : ℕ) (b : CertBound) (hb : b ∈ lowerHistoryFinalCuts row) :
    0 < certFieldVal b.threshold.c ∧
    0 ≤ certFieldVal b.threshold.x0 ∧ 0 ≤ certFieldVal b.threshold.x1 ∧
    0 ≤ certFieldVal b.threshold.y0 ∧ 0 ≤ certFieldVal b.threshold.y1 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  have h7 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 7)
  have hn7 := Real.sqrt_nonneg (7 : ℝ)
  have h21 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 21)
  have hn21 := Real.sqrt_nonneg (21 : ℝ)
  simp only [lowerHistoryFinalCuts] at hb
  split_ifs at hb <;> simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  all_goals rcases hb with rfl | rfl | rfl
  all_goals
    norm_num [lowerHistoryH7,lowerHistoryH9,lowerHistoryH2,lowerHistoryH5,lowerHistoryHN,
      lowerHistoryComplement,lowerHistoryPB,lowerHistoryWH,lowerHistoryAbs,lowerHistorySign,lowerHistoryQuadSign,lowerHistoryRatSign,lowerHistoryNeg,lowerHistoryThreshold,
      lowerHistorySort,lowerHistoryLex,lowerHistoryTheta,lowerHistoryCF,lowerHistoryMatrix,
      lowerHistoryDiv,lowerHistoryInv,lowerHistoryRat,lowerHistoryTau,lowerHistoryAlpha,
      lowerHistoryBeta,certFieldScale,certFieldAdd,certFieldSub,certFieldMul,certFieldVal]
    all_goals (repeat' constructor) <;> nlinarith

private theorem reached_final (hpull : LowerHistoryPullLaw) (t : ℝ) (h : ℕ → LowerPair)
    (n : ℕ) (hh : lowerHistory t h n) (base : LowerPair) (p : LowerHistoryPath)
    (hp : lowerHistoryStructural p) (hr : lowerHistoryReached t h n base p)
    (haz : lowerHistoryHazard p.row (h n)) : lowerHistoryFinalEvent base p := by
  obtain ⟨start,flip,hsum,hreal,_⟩ := hr
  have hn := (hreal.2.2.2 p.steps.length le_rfl).2.2
  rw [hsum] at hn
  have happ := Transfer15.replay_append base p p.steps.length
  have hw := (Transfer15.state_replay_shape p p.steps.length).2
  have hstate : (lowerHistoryStateAt p p.steps.length).wider = p.finalWider := by
    simpa [lowerHistoryStateAt,lowerHistoryFinalState] using hp.2.2.2.1.2.2.2
  rw [happ.1,happ.2,← hw,hstate] at hn
  have hcuts := final_cuts (h n) p.row haz
  intro b hb
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
  have hv := final_cut_fields p.row a ha
  apply (hpull base (lowerHistoryWordsAt p p.steps.length) a p.finalWider
    hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1 hv.2.2.2.2).mp
      (by
        dsimp only [lowerHistoryWordsAt]
        rw [← hn]
        intro b hb
        have he : b = a := by simpa using hb
        subst b
        exact hcuts a ha)
    _ (by simp)

end Final15

theorem solution (hpull : LowerHistoryPullLaw) (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n)
    (base : LowerPair) (p : LowerHistoryPath) (hp : lowerHistoryStructural p) (hr : lowerHistoryReached t h n base p) (haz : lowerHistoryHazard p.row (h n)) :
    lowerHistoryFinalEvent base p := by
  exact Final15.reached_final hpull t h n hh base p hp hr haz

#print axioms solution
