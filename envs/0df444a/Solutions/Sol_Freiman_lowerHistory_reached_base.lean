-- Prove2me | solution 1 for Freiman.lowerHistory_reached_base
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-13T13:27:30.82371+00:00
-- url     : https://prove2.me/submissions/abfb721e-a998-4c7e-9bb4-5229d296e3ae

import Definitions.Def_Freiman_lowerHistoryVerification
import Theorems.Thm_Freiman_lowerHistory_cf_value
import Theorems.Thm_Freiman_lowerHistory_sign_value
import Mathlib.Tactic
import Definitions.Def_Freiman_lowerInitialEntry
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
namespace Base15

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

private theorem normalize_idem (p : LowerPair) : lowerNormalize (lowerNormalize p) = lowerNormalize p := by
  unfold lowerNormalize
  split_ifs <;> simp_all
  all_goals (exfalso; linarith)

private theorem normal_wide (p : LowerPair) :
    lowerWidth (lowerNormalize p).2 ≤ lowerWidth (lowerNormalize p).1 := by
  unfold lowerNormalize
  split_ifs with hw
  · exact hw
  · exact (not_le.mp hw).le

private theorem hn_holds (base : LowerPair) (hn : lowerNormalize base = base) :
    lowerHistoryAtBase base [lowerHistoryHN] := by
  have hw : lowerWidth base.2 ≤ lowerWidth base.1 := by
    rw [← hn]
    exact normal_wide base
  simpa [lowerHistoryHN] using
    (lowerHistory_width_threshold base ([],[])).1.mp (by simpa using hw)

private theorem constant_bound (base : LowerPair) (q : ℚ) (lo strict : Bool) :
    certBoundHolds (lowerHistoryConstantBound q lo strict)
      (lowerRatio base.1) (lowerRatio base.2) (lowerScale base) ↔
      (if lo then if strict then (q:ℝ) < lowerScale base else (q:ℝ) ≤ lowerScale base
       else if strict then lowerScale base < (q:ℝ) else lowerScale base ≤ (q:ℝ)) := by
  simp [lowerHistoryConstantBound,lowerHistoryThreshold,lowerHistorySort,
    lowerHistoryLex,lowerHistoryRat,certBoundHolds,certThresholdVal,
    certThresholdNum,certThresholdDen,certFieldVal]

private theorem initial_base (hfamily : ∀ (f : LowerInitialFamily) (a k v : ℕ),
    lowerEntryDomain (lowerNormalize (lowerFamilyPair f a k v)))
    (base : LowerPair) (p : LowerHistoryPath) (hcat : p.catalog = .initial)
    (f : LowerInitialFamily) (a k v : ℕ)
    (hb : base = lowerNormalize (lowerFamilyPair f a k v)) : lowerHistoryBaseEvent base p := by
  have hd := hfamily f a k v
  rw [← hb] at hd
  have hn : lowerNormalize base = base := by rw [hb]; exact normalize_idem _
  refine ⟨[lowerHistoryZero,lowerHistoryHN,
    lowerHistoryConstantBound (729/1024) true true,
    lowerHistoryConstantBound (225/289) false true], ?_, ?_⟩
  · simp [lowerHistoryBasePremises,hcat]
  · have hz := zero_holds base
    have hw := hn_holds base hn
    have hlo := (constant_bound base (729/1024) true true).mpr (by simpa using hd.1)
    have hhi := (constant_bound base (225/289) false true).mpr (by simpa using hd.2.1)
    simpa [lowerHistoryAtBase,lowerHistoryConditions] using
      And.intro (hz _ (by simp)) (And.intro (hw _ (by simp)) (And.intro hlo hhi))

private theorem generic_base (hg : LowerHistoryGoodnessLaw)
    (q base : LowerPair) (p : LowerHistoryPath) (hi : p.catalog ≠ .initial)
    (hb : base = lowerNormalize q) (hgood : lowerGood q)
    (hfit : lowerHistoryContextFits base ⟨(p.context,[3,1]),(false,false)⟩)
    (ha3 : ¬lowerA q 3) (ha9 : ¬lowerA q 9) : lowerHistoryBaseEvent base p := by
  have hn : lowerNormalize base = base := by rw [hb]; exact normalize_idem _
  have hgn : lowerGood base := by
    simpa only [hb,lowerGood,lowerChild,normalize_idem] using hgood
  obtain ⟨bs,hbs,hholds⟩ := hg base _ hfit hn hgn
  refine ⟨[lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9]++bs,?_,?_⟩
  · simp [lowerHistoryBasePremises,hi,hbs]
  · have hz := zero_holds base
    have hw := hn_holds base hn
    have hvals := threshold_values q
    have hc7 : certBoundHolds lowerHistoryH7 (lowerRatio base.1) (lowerRatio base.2) (lowerScale base) := by
      change certThresholdVal lowerHistoryH7.threshold _ _ ≤ lowerScale base
      rw [hb,hvals.1]
      exact le_of_not_gt ha3
    have hc9 : certBoundHolds (lowerHistoryComplement lowerHistoryH9)
        (lowerRatio base.1) (lowerRatio base.2) (lowerScale base) := by
      change certThresholdVal lowerHistoryH9.threshold _ _ < lowerScale base
      rw [hb,hvals.2.1]
      exact lt_of_not_ge ha9
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl
      · exact hz _ (by simp)
      · exact hw _ (by simp)
      · exact hc7
      · exact hc9
    · exact hholds b hb

end Base15

open Freiman
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem offered_23_cuts (p : LowerPair)
    (ho : lowerOffered p (([2],[3]) : LowerLabel)) :
    ¬ lowerA p 3 ∧ ¬ lowerA p 9 := by
  have heq : ¬ lowerMixed p ∧ (([2],[3]) : LowerLabel) ∈ lowerEqualList p := by
    unfold lowerOffered at ho
    rcases ho with ho | ho
    · by_cases hm : lowerMixed p
      · rw [if_pos hm] at ho
        unfold lowerMixedList at ho
        repeat' split_ifs at ho
        all_goals simp_all
      · rw [if_neg hm] at ho
        exact ⟨hm,ho⟩
    · rcases ho.2 with ⟨k,hk,he⟩
      have hleft := congrArg List.length (congrArg Prod.fst he)
      have hright := congrArg List.length (congrArg Prod.snd he)
      simp at hleft hright
      subst k
      norm_num at he
  constructor
  · intro h3
    have hm := heq.2
    simp [lowerEqualList, h3] at hm
  · intro h9
    have h3 : ¬ lowerA p 3 := by
      intro h3
      have hm := heq.2
      simp [lowerEqualList, h3] at hm
    have hm := heq.2
    simp [lowerEqualList, h3, h9] at hm
    unfold lowerEarlyList at hm
    repeat' split_ifs at hm
    all_goals simp_all

private theorem birth_length (p : LowerPair) (l : LowerLabel) (wide : Bool)
    (heq : lowerNormalize (lowerChild p l) = lowerHistoryOrient
      (lowerHistoryRawStep (lowerNormalize p) false (([2],[3]) : LowerLabel)) wide) :
    l.1.length + l.2.length = 2 := by
  have he := congrArg (fun z : LowerPair => z.1.length + z.2.length) heq
  unfold lowerChild lowerHistoryRawStep lowerHistoryOrient lowerNormalize at he
  repeat' split_ifs at he
  all_goals simp at he ⊢ <;> omega

private theorem normalize_parity (p : LowerPair)
    (hp : (lowerNormalize p).1.length % 2 = (lowerNormalize p).2.length % 2) :
    ¬ lowerMixed p := by
  unfold lowerMixed lowerNormalize at *
  split_ifs at hp <;> simp_all

private theorem offered_a3_length (p : LowerPair) (l : LowerLabel)
    (hm : ¬ lowerMixed p) (ho : lowerOffered p l) (h3 : lowerA p 3) :
    l.1.length + l.2.length ≠ 2 := by
  unfold lowerOffered at ho
  rw [if_neg hm] at ho
  rcases ho with ho | ho
  · simp [lowerEqualList,h3] at ho
    rcases ho with rfl | rfl | ⟨_,rfl⟩ <;> decide
  · exact fun _ => ho.1.2.1 h3

private theorem offered_a9_length (p : LowerPair) (l : LowerLabel)
    (hm : ¬ lowerMixed p) (ho : lowerOffered p l) (h3 : ¬lowerA p 3)
    (h9 : lowerA p 9) (hlen : l.1.length + l.2.length = 2) :
    (¬ lowerL p ∧ (l = (([3],[2]) : LowerLabel) ∨ l = (([2],[2]) : LowerLabel))) ∨
      l = (([3],[3]) : LowerLabel) := by
  unfold lowerOffered at ho
  rw [if_neg hm] at ho
  rcases ho with ho | ho
  · simp [lowerEqualList,h3,h9] at ho
    by_cases hL : lowerL p
    · simp [hL] at ho
      rcases ho with rfl | rfl <;> simp at hlen
    · left
      refine ⟨hL,?_⟩
      simp [hL] at ho
      repeat' split_ifs at ho
      all_goals
        simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
      all_goals
        try {rcases ho with rfl | rfl | rfl <;> simp at hlen ⊢}
      all_goals
        unfold lowerEarlyList at ho
        repeat' split_ifs at ho
        all_goals simp_all [List.mem_append]
        all_goals aesop
  · right
    rcases ho.2 with ⟨k,hk,rfl⟩
    simp at hlen
    have : k = 1 := by omega
    subst k
    rfl
private theorem c32_forces_left (p : LowerPair) (wide : Bool)
    (hr : lowerEnds (lowerNormalize p).2 [3,1])
    (heq : lowerNormalize (lowerChild p (([3],[2]) : LowerLabel)) =
      lowerHistoryOrient
        (lowerHistoryRawStep (lowerNormalize p) false (([2],[3]) : LowerLabel)) wide) :
    lowerL p := by
  let q := lowerNormalize p
  change lowerEnds q.2 [3,1] at hr
  change lowerEnds q.1 [3,1]
  change lowerNormalize (q.1++[3],q.2++[2]) =
    lowerHistoryOrient (q.1++[2],q.2++[3]) wide at heq
  unfold lowerNormalize at heq
  split_ifs at heq <;> cases wide <;>
    simp only [lowerHistoryOrient, if_false, if_true] at heq
  all_goals rcases Prod.mk.inj heq with ⟨h1,h2⟩
  · have hx := List.append_cancel_left h1
    norm_num at hx
  · have hx := List.append_cancel_right h1
    simpa [hx] using hr
  · have hx := List.append_cancel_right h1
    simpa [hx] using hr
  · have hx := List.append_cancel_left h1
    norm_num at hx

private theorem c22_impossible (p : LowerPair) (wide : Bool)
    (heq : lowerNormalize (lowerChild p (([2],[2]) : LowerLabel)) =
      lowerHistoryOrient
        (lowerHistoryRawStep (lowerNormalize p) false (([2],[3]) : LowerLabel)) wide) : False := by
  let q := lowerNormalize p
  change lowerNormalize (q.1++[2],q.2++[2]) =
    lowerHistoryOrient (q.1++[2],q.2++[3]) wide at heq
  unfold lowerNormalize at heq
  split_ifs at heq <;> cases wide <;>
    simp only [lowerHistoryOrient, if_false, if_true] at heq
  all_goals rcases Prod.mk.inj heq with ⟨h1,h2⟩
  · have hx := List.append_cancel_left h2
    norm_num at hx
  · have hx := List.append_cancel_left (h2.trans h1)
    norm_num at hx
  · have hx := List.append_cancel_left (h1.trans h2)
    norm_num at hx
  · have hx := List.append_cancel_left h1
    norm_num at hx

private theorem c33_impossible (p : LowerPair) (wide : Bool)
    (heq : lowerNormalize (lowerChild p (([3],[3]) : LowerLabel)) =
      lowerHistoryOrient
        (lowerHistoryRawStep (lowerNormalize p) false (([2],[3]) : LowerLabel)) wide) : False := by
  let q := lowerNormalize p
  change lowerNormalize (q.1++[3],q.2++[3]) =
    lowerHistoryOrient (q.1++[2],q.2++[3]) wide at heq
  unfold lowerNormalize at heq
  split_ifs at heq <;> cases wide <;>
    simp only [lowerHistoryOrient, if_false, if_true] at heq
  all_goals rcases Prod.mk.inj heq with ⟨h1,h2⟩
  · have hx := List.append_cancel_left h1
    norm_num at hx
  · have hx := List.append_cancel_left (h1.trans h2)
    norm_num at hx
  · have hx := List.append_cancel_left (h2.trans h1)
    norm_num at hx
  · have hx := List.append_cancel_left h2
    norm_num at hx

private theorem birth_cuts (p : LowerPair) (l : LowerLabel) (wide : Bool)
    (hpar : (lowerNormalize p).1.length % 2 = (lowerNormalize p).2.length % 2)
    (hr : lowerEnds (lowerNormalize p).2 [3,1])
    (ho : lowerOffered p l)
    (heq : lowerNormalize (lowerChild p l) = lowerHistoryOrient
      (lowerHistoryRawStep (lowerNormalize p) false (([2],[3]) : LowerLabel)) wide) :
    ¬ lowerA p 3 ∧ ¬ lowerA p 9 := by
  have hm := normalize_parity p hpar
  have hlen := birth_length p l wide heq
  have h3 : ¬ lowerA p 3 := by
    intro ha
    exact offered_a3_length p l hm ho ha hlen
  refine ⟨h3,?_⟩
  intro h9
  rcases offered_a9_length p l hm ho h3 h9 hlen with hc | hc
  · rcases hc with ⟨hnL,rfl | rfl⟩
    · exact hnL (c32_forces_left p wide hr heq)
    · exact c22_impossible p wide heq
  · subst l
    exact c33_impossible p wide heq


private theorem reached_generic_cuts (t : ℝ) (h : ℕ → LowerPair) (n : ℕ)
    (hh : lowerHistory t h n) (base : LowerPair) (p : LowerHistoryPath)
    (hr : lowerHistoryReached t h n base p) (hi : p.catalog ≠ .initial) :
    ∃ q : LowerPair, base = lowerNormalize q ∧ lowerGood q ∧
      ¬ lowerA q 3 ∧ ¬ lowerA q 9 := by
  rcases hr with ⟨start,flip,hlen,hreal,hentry⟩
  rw [if_neg hi] at hentry
  have hstart : 0 < start := hentry.1
  let m := start - 1
  have hm1 : m + 1 = start := by dsimp [m]; omega
  have hmn : m < n := by omega
  obtain ⟨l,ho,hpriority,hchild⟩ := hh.2.2 m hmn
  have hs := hh.2.1 m (by omega)
  have hpar : (lowerNormalize (h m)).1.length % 2 =
      (lowerNormalize (h m)).2.length % 2 := by
    rw [← hentry.2.1]
    exact hreal.2.2.1
  have hright : lowerEnds (lowerNormalize (h m)).2 [3,1] := by
    rw [← hentry.2.1]
    have hb := hreal.2.1
    rw [if_neg hi] at hb
    exact hb.1
  have heq : lowerNormalize (lowerChild (h m) l) = lowerHistoryOrient
      (lowerHistoryRawStep (lowerNormalize (h m)) false (([2],[3]) : LowerLabel))
      p.initialWider := by
    rw [← hchild, hm1]
    have hj := hreal.2.2.2 0 (by omega)
    simpa [lowerHistoryReplay,hentry.2.2.2,hentry.2.1] using hj.2.2
  have hc := birth_cuts (h m) l p.initialWider hpar hright ho heq
  exact ⟨h m,hentry.2.1,hs.2.1,hc.1,hc.2⟩


theorem solution (hfamily : ∀ (f : LowerInitialFamily) (a k v : ℕ), lowerEntryDomain (lowerNormalize (lowerFamilyPair f a k v))) (hg : LowerHistoryGoodnessLaw) (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n)
    (base : LowerPair) (p : LowerHistoryPath) (hp : lowerHistoryStructural p) (hr : lowerHistoryReached t h n base p) :
    lowerHistoryBaseEvent base p := by
  by_cases hi : p.catalog = .initial
  · obtain ⟨start, flip, hlen, hreal, hentry⟩ := hr
    rw [if_pos hi] at hentry
    obtain ⟨hstart, f, a, k, v, hselected, hbselected, hb, hchild⟩ := hentry
    exact Base15.initial_base hfamily base p hi f a k v hb
  · obtain ⟨q, hb, hgood, h3, h9⟩ := reached_generic_cuts t h n hh base p hr hi
    exact Base15.generic_base hg q base p hi hb hgood
      (Transfer15.reached_context t h n base p hr hi) h3 h9

#print axioms solution
