-- Prove2me | solution 1 for Freiman.lowerHistory_comparison_transfer
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-13T12:46:31.842349+00:00
-- url     : https://prove2.me/submissions/6bc64925-8187-46f9-8f1b-504a531d8a82

import Definitions.Def_Freiman_lowerHistoryVerification
import Theorems.Thm_Freiman_lowerHistory_cf_value
import Theorems.Thm_Freiman_lowerHistory_sign_value
import Mathlib.Tactic
import Definitions.Def_Freiman_lowerCover
import Theorems.Thm_Freiman_prefixEval_difference
import Theorems.Thm_Freiman_prefixEval_mobius
import Theorems.Thm_Freiman_continuant_determinant
import Theorems.Thm_Freiman_continuant_denominator_pos
import Theorems.Thm_Freiman_lowerEarlyTerminal_ratio_range
import Theorems.Thm_Freiman_lowerEarlyTerminal_endpoint_swap_nontie
import Theorems.Thm_Freiman_lowerEarlyTerminal_ratio_append


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
namespace CDUnique15

private def GoodHead : List ℕ+ → Prop
  | [] => True
  | a :: _ => 2 ≤ (a : ℕ)

private theorem goodHead_prefix (u v : List ℕ+) (h : GoodHead (u ++ v)) : GoodHead u := by
  cases u with
  | nil => trivial
  | cons a u => exact h

private theorem goodHead_append (u v : List ℕ+) (hu : GoodHead u) (hne : u ≠ []) :
    GoodHead (u ++ v) := by
  cases u with
  | nil => exact (hne rfl).elim
  | cons a u => exact hu

private theorem cd_snoc (w : List ℕ+) (a : ℕ+) :
    lowerCD (w ++ [a]) =
      ((lowerCD w).2, (lowerCD w).1 + (a : ℕ) * (lowerCD w).2) := by
  unfold lowerCD
  simp [List.foldl_append]

private theorem snd_pos (w : List ℕ+) : 0 < (lowerCD w).2 := by
  induction w using List.reverseRecOn with
  | nil => decide
  | append_singleton w a ih =>
      rw [cd_snoc]
      have hp := Nat.mul_pos a.pos ih
      dsimp only
      omega

private theorem fst_pos (w : List ℕ+) (h : w ≠ []) : 0 < (lowerCD w).1 := by
  induction w using List.reverseRecOn with
  | nil => exact (h rfl).elim
  | append_singleton w a ih =>
      rw [cd_snoc]
      exact snd_pos w

private theorem cd_strict (w : List ℕ+) (h : GoodHead w) : (lowerCD w).1 < (lowerCD w).2 := by
  induction w using List.reverseRecOn with
  | nil => decide
  | append_singleton w a ih =>
      rw [cd_snoc]
      dsimp only
      by_cases hw : w = []
      · subst w
        have ha : 2 ≤ (a : ℕ) := h
        simpa [lowerCD] using (show 1 < (a : ℕ) by omega)
      · have hp := fst_pos w hw
        have hm := Nat.le_mul_of_pos_left (lowerCD w).2 a.pos
        omega

private theorem injective (u v : List ℕ+) (hu : GoodHead u) (hv : GoodHead v)
    (heq : lowerCD u = lowerCD v) : u = v := by
  induction u using List.reverseRecOn generalizing v with
  | nil =>
      by_cases hn : v = []
      · exact hn.symm
      · have hp := fst_pos v hn
        have hz := congrArg Prod.fst heq
        change 0 = (lowerCD v).1 at hz
        omega
  | append_singleton u a ih =>
      rcases List.eq_nil_or_concat' v with rfl | ⟨v,b,rfl⟩
      · have hz := congrArg Prod.fst heq
        rw [cd_snoc] at hz
        have hp := snd_pos u
        change (lowerCD u).2 = 0 at hz
        omega
      · have hgu := goodHead_prefix u [a] hu
        have hgv := goodHead_prefix v [b] hv
        have hdu := cd_strict u hgu
        have hdv := cd_strict v hgv
        have hs := congrArg Prod.fst heq
        have ht := congrArg Prod.snd heq
        rw [cd_snoc,cd_snoc] at hs ht
        dsimp only at hs ht
        have hm := congrArg (fun z : ℕ × ℕ => z.2 % z.1) heq
        rw [cd_snoc,cd_snoc] at hm
        simp only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hdu,
          Nat.mod_eq_of_lt hdv] at hm
        have hc : lowerCD u = lowerCD v := Prod.ext hm hs
        have huv := ih v hgu hgv hc
        subst v
        have hab : (a : ℕ) = (b : ℕ) := by
          apply Nat.eq_of_mul_eq_mul_right (snd_pos u)
          exact Nat.add_left_cancel ht
        have hab' : a = b := Subtype.ext hab
        rw [hab']

private theorem core_append_head (c : LowerPair) (hc : c ∈ lowerCores)
    (u v : List ℕ+) : GoodHead (c.1 ++ u) ∧ GoodHead (c.2 ++ v) := by
  simp only [lowerCores, List.mem_append, List.mem_map] at hc
  rcases hc with hc | ⟨d,hd,rfl⟩
  · simp only [lowerBaseCores, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [GoodHead]
  · simp only [lowerBaseCores, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [GoodHead]

private theorem admissible_goodHead (p : LowerPair) (hp : lowerAdmissible p) :
    GoodHead p.1 ∧ GoodHead p.2 := by
  rcases hp.1 with ⟨c,hc,u,v,rfl,hu,hv⟩
  exact core_append_head c hc u v

end CDUnique15


open Freiman

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Transfer15

private theorem nonempty_of_ratio_pos (w : List ℕ+) (h : 0 < lowerRatio w) : w ≠ [] := by
  intro hw
  subst w
  norm_num [lowerRatio, lowerCD] at h

private theorem normalize_heads (z : LowerPair)
    (hh : CDUnique15.GoodHead z.1 ∧ CDUnique15.GoodHead z.2) :
    CDUnique15.GoodHead (lowerNormalize z).1 ∧
      CDUnique15.GoodHead (lowerNormalize z).2 := by
  unfold lowerNormalize
  split <;> simp_all

private theorem normalize_nonempty (z : LowerPair) (hh : z.1 ≠ [] ∧ z.2 ≠ []) :
    (lowerNormalize z).1 ≠ [] ∧ (lowerNormalize z).2 ≠ [] := by
  unfold lowerNormalize
  split <;> simp_all

private theorem comparison_transfer_of_alignments
    (hleft : ∀ (P1 P2 : List ℕ+),
      P1.length % 2 = P2.length % 2 →
      CDUnique15.GoodHead P1 → CDUnique15.GoodHead P2 → P1 ≠ [] → P2 ≠ [] →
      (if P1.length % 2 = 0 then
        lowerEndpoint (P2 ++ [2], P1 ++ [1]) false ≤
          lowerEndpoint (P1 ++ [1], P2 ++ [2]) false
       else
        lowerEndpoint (P1 ++ [1], P2 ++ [2]) true ≤
          lowerEndpoint (P2 ++ [2], P1 ++ [1]) true))
    (hmixed : ∀ (P1 P2 : List ℕ+),
      P1.length % 2 ≠ P2.length % 2 →
      CDUnique15.GoodHead P1 → CDUnique15.GoodHead P2 → P1 ≠ [] → P2 ≠ [] →
      (if P2.length % 2 = 0 then
        lowerEndpoint (P2 ++ [2], P1 ++ [2]) false ≤
          lowerEndpoint (P1 ++ [2], P2 ++ [2]) false
       else
        lowerEndpoint (P1 ++ [2], P2 ++ [2]) true ≤
          lowerEndpoint (P2 ++ [2], P1 ++ [2]) true))
    (hg : LowerHistoryGreaterLaw) (he : LowerHistoryEndpointLaw)
    (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n)
    (base : LowerPair) (p : LowerHistoryPath) (hp : lowerHistoryStructural p)
    (hr : lowerHistoryReached t h n base p) (hi : p.catalog ≠ .initial)
    (hrow : p.row ≠ 4) (ha : lowerHistoryEarlierAnchor base p t)
    (hc : lowerHistoryComparisonsHold p (lowerRatio base.1)
      (lowerRatio base.2) (lowerScale base)) :
    lowerHistoryTarget p.row (h n) t := by
  classical
  have hfit := reached_context t h n base p hr hi
  have hnum := endpoint_compare hg he base p hfit hc
  have hanc :
      lowerHistoryEndpointReal base ⟨(p.context,[3,1]),(false,false)⟩
          (if ([3,1] : List ℕ+).IsSuffix p.context then ([],[]) else ([3],[2]))
          (decide (¬ ([3,1] : List ℕ+).IsSuffix p.context)) ≤
        (if base.1.length % 2 = 0 then t else -t) := ha
  have hgoal :
      lowerHistoryEndpointReal base ⟨(p.context,[3,1]),(false,false)⟩
          ((lowerHistoryFinalWords p).1 ++ (if p.row = 1 then [1] else [2]),
           (lowerHistoryFinalWords p).2 ++ (if p.row = 4 then [1] else [2])) false ≤
        (if base.1.length % 2 = 0 then t else -t) := hnum.trans hanc
  rcases hr with ⟨start, flip, hsum, hreal, hentry⟩
  unfold lowerHistoryRealizes at hreal
  simp only [hi, if_false] at hreal
  rcases hreal with ⟨hctx, hrctx, hbasepar, hreal⟩
  have hrn := hreal p.steps.length le_rfl
  rw [hsum] at hrn
  have happ := (replay_append base p p.steps.length).1
  have happWide := (replay_append base p p.steps.length).2
  have hshape := state_replay_shape p p.steps.length
  have hshape' :
      (lowerHistoryFinalState p).context.parity =
          (decide ((lowerHistoryReplay ([],[]) p p.steps.length).1.1.length % 2 = 1),
           decide ((lowerHistoryReplay ([],[]) p p.steps.length).1.2.length % 2 = 1)) ∧
      (lowerHistoryFinalState p).wider =
          (lowerHistoryReplay ([],[]) p p.steps.length).2 := by
    simpa only [lowerHistoryStateAt, lowerHistoryFinalState, List.take_length] using hshape
  have hfinal := hp.2.2.2.1
  dsimp only at hfinal
  have hparity :
      (decide ((lowerHistoryReplay ([],[]) p p.steps.length).1.1.length % 2 = 1),
       decide ((lowerHistoryReplay ([],[]) p p.steps.length).1.2.length % 2 = 1)) =
        p.finalParity := by
    rw [← hshape'.1, hfinal.2.2.1]
  have hwide : (lowerHistoryReplay ([],[]) p p.steps.length).2 = p.finalWider := by
    rw [← hshape'.2, hfinal.2.2.2]
  have hnorm : lowerNormalize (h n) = lowerHistoryOrient
      (lowerHistoryAppend base (lowerHistoryReplay ([],[]) p p.steps.length).1)
      p.finalWider := by
    calc
      lowerNormalize (h n) = lowerHistoryOrient
          (lowerHistoryReplay base p p.steps.length).1
          (lowerHistoryReplay base p p.steps.length).2 := hrn.2.2
      _ = lowerHistoryOrient
          (lowerHistoryAppend base (lowerHistoryReplay ([],[]) p p.steps.length).1)
          (lowerHistoryReplay ([],[]) p p.steps.length).2 := by rw [happ, happWide]
      _ = _ := by rw [hwide]
  have hs := hh.2.1 n le_rfl
  have hheads := normalize_heads (h n) (CDUnique15.admissible_goodHead _ hs.1)
  have hne0 : (h n).1 ≠ [] ∧ (h n).2 ≠ [] := by
    refine ⟨nonempty_of_ratio_pos _ ?_, nonempty_of_ratio_pos _ ?_⟩
    · linarith [hs.2.2.2.1]
    · linarith [hs.2.2.2.2.2.1]
  have hne := normalize_nonempty (h n) hne0
  have hcat := hp.2.2.2.2
  rw [if_neg hi] at hcat
  rcases hcat with hleftcase | hrightcase | hmixedcase | hrightMixed
  · rcases hleftcase with ⟨_, hrow1, hfp, hfw⟩
    rw [hrow1] at hgoal ⊢
    simp only [lowerHistoryTarget]
    rw [hfw] at hnorm
    simp only [lowerHistoryOrient, ↓reduceIte] at hnorm
    rw [hfp] at hparity
    simp only [Prod.mk.injEq] at hparity
    have hw1 := even_of_decide_not_odd _ hparity.1
    have hw2 := even_of_decide_not_odd _ hparity.2
    rw [hnorm] at hheads hne
    simp only [lowerHistoryAppend, Prod.fst, Prod.snd] at hheads hne
    have hab : (base.1 ++ (lowerHistoryReplay ([],[]) p p.steps.length).1.1).length % 2 =
        (base.2 ++ (lowerHistoryReplay ([],[]) p p.steps.length).1.2).length % 2 := by
      simp [List.length_append, Nat.add_mod, hw1, hw2, hbasepar]
    have hal := hleft
      (base.1 ++ (lowerHistoryReplay ([],[]) p p.steps.length).1.1)
      (base.2 ++ (lowerHistoryReplay ([],[]) p p.steps.length).1.2)
      hab hheads.2 hheads.1 hne.2 hne.1
    have hcoord : lowerLocalCoordinate (h n) t =
        (if base.1.length % 2 = 0 then t else -t) := by
      unfold lowerLocalCoordinate
      rw [hnorm]
      simp [lowerHistoryAppend, List.length_append, Nat.add_mod, hw2, hbasepar]
    rw [hcoord]
    unfold lowerLocalLower lowerChild
    rw [hnorm]
    unfold lowerHistoryEndpointReal lowerHistoryCommonOdd lowerHistoryFinalWords at hgoal
    simp only [lowerHistoryAppend, lowerHistoryOrient, ↓reduceIte, Prod.fst, Prod.snd,
      List.reverse_cons, List.reverse_nil, List.nil_append]
    rcases Nat.mod_two_eq_zero_or_one base.1.length with hb | hb
    · have hb2 : base.2.length % 2 = 0 := hbasepar ▸ hb
      simp [hb, hb2, List.length_append, Nat.add_mod, hw1, hw2] at hal hgoal ⊢
      exact hal.trans (by simpa [lowerHistoryAppend, List.append_assoc] using hgoal)
    · have hb2 : base.2.length % 2 = 1 := hbasepar ▸ hb
      simp [hb, hb2, List.length_append, Nat.add_mod, hw1, hw2] at hal hgoal ⊢
      have hg' : t ≤ lowerEndpoint
          (base.1 ++ ((lowerHistoryReplay ([],[]) p p.steps.length).1.1 ++ [1]),
           base.2 ++ ((lowerHistoryReplay ([],[]) p p.steps.length).1.2 ++ [2])) true := by
        simpa [lowerHistoryAppend, List.append_assoc] using hgoal
      exact hg'.trans hal
  · rcases hrightcase with ⟨_, hrow2, hfp, hfw⟩
    rw [hrow2] at hgoal ⊢
    simp only [lowerHistoryTarget]
    rw [hfw] at hnorm
    simp only [lowerHistoryOrient, Bool.false_eq_true, ↓reduceIte] at hnorm
    rw [hfp] at hparity
    simp only [Prod.mk.injEq] at hparity
    have hw1 := even_of_decide_not_odd _ hparity.1
    have hcoord : lowerLocalCoordinate (h n) t =
        (if base.1.length % 2 = 0 then t else -t) := by
      unfold lowerLocalCoordinate
      rw [hnorm]
      simp only [lowerHistoryAppend, Prod.fst, List.length_append, Nat.add_mod, hw1,
        Nat.add_zero, Nat.mod_mod]
    rw [hcoord]
    unfold lowerLocalLower lowerChild
    rw [hnorm]
    unfold lowerHistoryEndpointReal lowerHistoryCommonOdd lowerHistoryFinalWords at hgoal
    simp only [lowerHistoryAppend, lowerHistoryOrient, Bool.false_eq_true, ↓reduceIte,
      Prod.fst, Prod.snd, List.reverse_cons, List.reverse_nil, List.nil_append]
    rcases Nat.mod_two_eq_zero_or_one base.1.length with hb | hb <;>
      simp [hb, List.length_append, Nat.add_mod, hw1] at hgoal ⊢
    all_goals simpa [lowerHistoryAppend, List.append_assoc] using hgoal
  · rcases hmixedcase with ⟨_, hrow3, hfp, hfw⟩
    rw [hrow3] at hgoal ⊢
    simp only [lowerHistoryTarget]
    rw [hfw] at hnorm
    simp only [lowerHistoryOrient, ↓reduceIte] at hnorm
    rw [hfp] at hparity
    simp only [Prod.mk.injEq] at hparity
    have hw1 : (lowerHistoryReplay ([],[]) p p.steps.length).1.1.length % 2 = 1 :=
      of_decide_eq_true hparity.1
    have hw2 := even_of_decide_not_odd _ hparity.2
    rw [hnorm] at hheads hne
    simp only [lowerHistoryAppend, Prod.fst, Prod.snd] at hheads hne
    have hab : (base.1 ++ (lowerHistoryReplay ([],[]) p p.steps.length).1.1).length % 2 ≠
        (base.2 ++ (lowerHistoryReplay ([],[]) p p.steps.length).1.2).length % 2 := by
      simp only [List.length_append, Nat.add_mod, hw1, hw2, Nat.add_zero, Nat.mod_mod]
      omega
    have hal := hmixed
      (base.1 ++ (lowerHistoryReplay ([],[]) p p.steps.length).1.1)
      (base.2 ++ (lowerHistoryReplay ([],[]) p p.steps.length).1.2)
      hab hheads.2 hheads.1 hne.2 hne.1
    have hcoord : lowerLocalCoordinate (h n) t =
        (if base.1.length % 2 = 0 then t else -t) := by
      unfold lowerLocalCoordinate
      rw [hnorm]
      simp [lowerHistoryAppend, List.length_append, Nat.add_mod, hw2, hbasepar]
    rw [hcoord]
    unfold lowerLocalLower lowerChild
    rw [hnorm]
    unfold lowerHistoryEndpointReal lowerHistoryCommonOdd lowerHistoryFinalWords at hgoal
    simp only [lowerHistoryAppend, lowerHistoryOrient, ↓reduceIte, Prod.fst, Prod.snd,
      List.reverse_cons, List.reverse_nil, List.nil_append]
    rcases Nat.mod_two_eq_zero_or_one base.1.length with hb | hb
    · have hb2 : base.2.length % 2 = 0 := hbasepar ▸ hb
      simp [hb, hb2, List.length_append, Nat.add_mod, hw1, hw2] at hal hgoal ⊢
      exact hal.trans (by simpa [lowerHistoryAppend, List.append_assoc] using hgoal)
    · have hb2 : base.2.length % 2 = 1 := hbasepar ▸ hb
      simp [hb, hb2, List.length_append, Nat.add_mod, hw1, hw2] at hal hgoal ⊢
      have hg' : t ≤ lowerEndpoint
          (base.1 ++ ((lowerHistoryReplay ([],[]) p p.steps.length).1.1 ++ [2]),
           base.2 ++ ((lowerHistoryReplay ([],[]) p p.steps.length).1.2 ++ [2])) true := by
        simpa [lowerHistoryAppend, List.append_assoc] using hgoal
      exact hg'.trans hal
  · exact (hrow hrightMixed.2.1).elim

end Transfer15



namespace TieAlgebra14

private def A (c d : ℝ) : ℝ := 4*c*d - 3*c^2
private def B (c d : ℝ) : ℝ := 2*d^2 - 4*c*d + 5*c^2
private def cross (c1 d1 c2 d2 : ℝ) : ℝ := c1*d2 - c2*d1
private def factor (c1 d1 c2 d2 : ℝ) : ℝ :=
  4*c1*c2 + 3*c1*d2 + 3*c2*d1 - 4*d1*d2

private theorem resultant {c1 d1 c2 d2 : ℝ}
    (hA : A c1 d1 = A c2 d2) (hB : B c1 d1 = B c2 d2) :
    cross c1 d1 c2 d2 * factor c1 d1 c2 d2 = 0 := by
  have h : A c1 d1 * B c2 d2 - A c2 d2 * B c1 d1 = 0 := by rw [hA, hB]; ring
  have hid : A c1 d1 * B c2 d2 - A c2 d2 * B c1 d1 =
      -2 * cross c1 d1 c2 d2 * factor c1 d1 c2 d2 := by
    simp only [A, B, cross, factor]
    ring
  rw [hid] at h
  nlinarith

private theorem finish {c1 d1 c2 d2 : ℝ}
    (hd1 : 0 < d1) (hd2 : 0 < d2)
    (hB : B c1 d1 = B c2 d2)
    (hcross : cross c1 d1 c2 d2 = 0) : c1 = c2 ∧ d1 = d2 := by
  have hid : B c1 d1 * d2^2 - B c2 d2 * d1^2 =
      cross c1 d1 c2 d2 *
        (-4*d1*d2 + 5*c1*d2 + 5*c2*d1) := by
    simp only [B, cross]
    ring
  rw [hcross] at hid
  have hweighted : B c1 d1 * d2^2 = B c2 d2 * d1^2 := by
    linarith
  have hsame : B c2 d2 * d1^2 = B c2 d2 * d2^2 := by
    calc
      B c2 d2 * d1^2 = B c1 d1 * d2^2 := hweighted.symm
      _ = B c2 d2 * d2^2 := by rw [hB]
  have hBpos : 0 < B c2 d2 := by
    have hs : 0 < d2^2 := sq_pos_of_pos hd2
    have h1 := sq_nonneg (d2 - 2*c2)
    have h2 := sq_nonneg c2
    simp only [B]
    nlinarith
  have hdsq : d1^2 = d2^2 := by nlinarith [hsame]
  have hd : d1 = d2 := by nlinarith
  have hcprod : (c1-c2)*d2 = 0 := by
    simp only [cross] at hcross
    rw [hd] at hcross
    nlinarith
  have hc : c1 = c2 := by
    rcases mul_eq_zero.mp hcprod with h | h
    · linarith
    · exact (ne_of_gt hd2 h).elim
  exact ⟨hc, hd⟩

private theorem injective_below_twice
    {c1 d1 c2 d2 : ℝ}
    (hd1 : 0 < d1) (hd2 : 0 < d2) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (hA : 4*c1*d1 - 3*c1^2 = 4*c2*d2 - 3*c2^2)
    (hB : 2*d1^2 - 4*c1*d1 + 5*c1^2 = 2*d2^2 - 4*c2*d2 + 5*c2^2)
    (h1 : d1 < 2*c1) (h2 : d2 < 2*c2) : c1 = c2 ∧ d1 = d2 := by
  have hres := resultant (c1 := c1) (d1 := d1) (c2 := c2) (d2 := d2) hA hB
  have hg1 : 0 < 2*c1-d1 := by linarith
  have hg2 : 0 < 2*c2-d2 := by linarith
  have hp1 : 0 < (2*c1-d1)*(2*c2-d2) := mul_pos hg1 hg2
  have hp2 : 0 < (2*c1-d1)*d2 := mul_pos hg1 hd2
  have hp3 : 0 < (2*c2-d2)*d1 := mul_pos hg2 hd1
  have hfac : 0 < factor c1 d1 c2 d2 := by
    simp only [factor]
    nlinarith
  have hcross : cross c1 d1 c2 d2 = 0 :=
    (mul_eq_zero.mp hres).resolve_right (ne_of_gt hfac)
  exact finish hd1 hd2 hB hcross

private theorem injective_above_twice
    {c1 d1 c2 d2 : ℝ}
    (hd1 : 0 < d1) (hd2 : 0 < d2) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (hA : 4*c1*d1 - 3*c1^2 = 4*c2*d2 - 3*c2^2)
    (hB : 2*d1^2 - 4*c1*d1 + 5*c1^2 = 2*d2^2 - 4*c2*d2 + 5*c2^2)
    (h1 : 2*c1 < d1) (h2 : 2*c2 < d2) : c1 = c2 ∧ d1 = d2 := by
  have hres := resultant (c1 := c1) (d1 := d1) (c2 := c2) (d2 := d2) hA hB
  have hg1 : 0 < d1-2*c1 := by linarith
  have hg2 : 0 < d2-2*c2 := by linarith
  have hp : 0 < (d1-2*c1)*(d2-2*c2) := mul_pos hg1 hg2
  have hle1 : d1-2*c1 ≤ d1 := by linarith
  have hle2 : d2-2*c2 ≤ d2 := by linarith
  have hp1 : (d1-2*c1)*(d2-2*c2) ≤ (d1-2*c1)*d2 :=
    mul_le_mul_of_nonneg_left hle2 hg1.le
  have hp2 : (d1-2*c1)*(d2-2*c2) ≤ (d2-2*c2)*d1 := by
    nlinarith [mul_le_mul_of_nonneg_right hle1 hg2.le]
  have hfac : factor c1 d1 c2 d2 < 0 := by
    simp only [factor]
    nlinarith
  have hcross : cross c1 d1 c2 d2 = 0 :=
    (mul_eq_zero.mp hres).resolve_right (ne_of_lt hfac)
  exact finish hd1 hd2 hB hcross


end TieAlgebra14


open Freiman
namespace M7TieWidth14
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

private noncomputable def den (w : List ℕ+) : ℝ :=
  (((lowerCD w).2 : ℝ) + lowerBeta * (lowerCD w).1) *
    (((lowerCD w).2 : ℝ) + lowerAlpha * (lowerCD w).1)

private def coeffA (w : List ℕ+) : ℚ :=
  4 * ((lowerCD w).1 : ℚ) * (lowerCD w).2 - 3 * ((lowerCD w).1 : ℚ)^2
private def coeffB (w : List ℕ+) : ℚ :=
  2 * ((lowerCD w).2 : ℚ)^2 - 4 * ((lowerCD w).1 : ℚ) * (lowerCD w).2 +
    5 * ((lowerCD w).1 : ℚ)^2

private theorem width_eq (w : List ℕ+) : lowerWidth w = (lowerBeta-lowerAlpha) / den w := by
  unfold lowerWidth
  rw [prefixEval_difference w lowerBeta lowerAlpha tails.2.1 tails.1,
    abs_of_pos (sub_pos.mpr tails.2.2)]
  simp only [den, cd_eq]

private theorem den_coefficients (w : List ℕ+) :
    den w = (3 * (coeffB w : ℝ) + Real.sqrt 21 * (coeffA w : ℝ)) / 6 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 21)
  simp only [den, coeffA, coeffB, lowerAlpha, lowerBeta]
  push_cast
  linear_combination (((lowerCD w).1 : ℝ)^2 / 12) * hs

private theorem rational_coefficients (a b : ℚ)
    (h : (a : ℝ) + Real.sqrt 21 * (b : ℝ) = 0) : a = 0 ∧ b = 0 := by
  have hi : Irrational (Real.sqrt (21:ℝ)) := by norm_num
  by_cases hb : b = 0
  · subst b
    simp only [Rat.cast_zero, mul_zero, add_zero] at h
    exact ⟨by exact_mod_cast h,rfl⟩
  · exfalso
    apply hi
    refine ⟨-a/b, ?_⟩
    push_cast
    have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb
    apply (div_eq_iff hb').mpr
    linarith

private theorem coefficients_of_width (u v : List ℕ+) (hw : lowerWidth u = lowerWidth v) :
    coeffA u = coeffA v ∧ coeffB u = coeffB v := by
  have hd : den u = den v := by
    apply inv_injective
    apply mul_left_cancel₀ (ne_of_gt (sub_pos.mpr tails.2.2))
    simpa only [width_eq, div_eq_mul_inv] using hw
  rw [den_coefficients,den_coefficients] at hd
  have hlin : ((3*(coeffB u-coeffB v) : ℚ) : ℝ) +
      Real.sqrt 21 * ((coeffA u-coeffA v : ℚ) : ℝ) = 0 := by
    push_cast
    linarith
  obtain ⟨hb,ha⟩ := rational_coefficients _ _ hlin
  constructor <;> linarith

private theorem cd_eq_of_width_same_side (u v : List ℕ+) (hw : lowerWidth u = lowerWidth v)
    (hside : ((1/2:ℝ) < lowerRatio u ∧ (1/2:ℝ) < lowerRatio v) ∨
      (lowerRatio u < (1/2:ℝ) ∧ lowerRatio v < (1/2:ℝ))) :
    lowerCD u = lowerCD v := by
  have hcoeff := coefficients_of_width u v hw
  have hA : 4*((lowerCD u).1:ℝ)*(lowerCD u).2-3*((lowerCD u).1:ℝ)^2 =
      4*((lowerCD v).1:ℝ)*(lowerCD v).2-3*((lowerCD v).1:ℝ)^2 := by
    have h := hcoeff.1
    dsimp only [coeffA] at h
    exact_mod_cast h
  have hB : 2*((lowerCD u).2:ℝ)^2-4*((lowerCD u).1:ℝ)*(lowerCD u).2+5*((lowerCD u).1:ℝ)^2 =
      2*((lowerCD v).2:ℝ)^2-4*((lowerCD v).1:ℝ)*(lowerCD v).2+5*((lowerCD v).1:ℝ)^2 := by
    have h := hcoeff.2
    dsimp only [coeffB] at h
    exact_mod_cast h
  have heq : ((lowerCD u).1:ℝ) = ((lowerCD v).1:ℝ) ∧
      ((lowerCD u).2:ℝ) = ((lowerCD v).2:ℝ) := by
    rcases hside with ⟨hu,hv⟩ | ⟨hu,hv⟩
    · apply TieAlgebra14.injective_below_twice (q_pos u) (q_pos v)
        (Nat.cast_nonneg _) (Nat.cast_nonneg _) hA hB
      · have hx := (lt_div_iff₀ (q_pos u)).mp hu
        linarith
      · have hx := (lt_div_iff₀ (q_pos v)).mp hv
        linarith
    · apply TieAlgebra14.injective_above_twice (q_pos u) (q_pos v)
        (Nat.cast_nonneg _) (Nat.cast_nonneg _) hA hB
      · have hx := (div_lt_iff₀ (q_pos u)).mp hu
        linarith
      · have hx := (div_lt_iff₀ (q_pos v)).mp hv
        linarith
  apply Prod.ext
  · exact_mod_cast heq.1
  · exact_mod_cast heq.2

end M7TieWidth14


open Freiman
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace M7Ties15

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

private theorem width_formula (w : List ℕ+) :
    lowerWidth w = (lowerBeta - lowerAlpha) /
      ((((lowerCD w).1 : ℝ) * lowerAlpha + (lowerCD w).2) *
       (((lowerCD w).1 : ℝ) * lowerBeta + (lowerCD w).2)) := by
  unfold lowerWidth
  rw [prefixEval_difference w lowerBeta lowerAlpha tails.2.1 tails.1]
  rw [abs_of_pos (sub_pos.mpr tails.2.2), cd_eq]
  ring

private theorem width_pos (w : List ℕ+) : 0 < lowerWidth w := by
  rw [width_formula]
  have ha := tails.1.1
  have hb := tails.2.1.1
  have hq := q_pos w
  exact div_pos (sub_pos.mpr tails.2.2) (mul_pos (by positivity) (by positivity))

private theorem width_eq_of_cd (u v : List ℕ+) (h : lowerCD u = lowerCD v) :
    lowerWidth u = lowerWidth v := by rw [width_formula, width_formula, h]

private theorem pe_append : ∀ (u v : List ℕ+) (x : ℝ),
    prefixEval (u ++ v) x = prefixEval u (prefixEval v x)
  | [], _, _ => rfl
  | _ :: u, v, x => by simp only [List.cons_append, prefixEval, pe_append u v x]

private theorem radical3 :
    let s := Real.sqrt (3 : ℝ)
    s^2 = 3 ∧ 0 < s ∧ s < 2 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  dsimp
  refine ⟨hs, by nlinarith, by nlinarith⟩

private theorem endpoint_tails :
    let E := prefixEval [1,3] lowerTau
    let F := prefixEval [1,2,1,3] lowerTau
    E = (3 + Real.sqrt 3) / 6 ∧ F = (52 + Real.sqrt 3) / 73 ∧
      F < E ∧ E ∈ Set.Icc (0 : ℝ) 1 ∧ F ∈ Set.Icc (0 : ℝ) 1 := by
  have hs := radical3.1
  have hp := radical3.2.1
  have hh := radical3.2.2
  have h3 : (1:ℝ) / (3 + (Real.sqrt 3 - 1)) = 2 - Real.sqrt 3 := by
    field_simp [show (3:ℝ) + (Real.sqrt 3 - 1) ≠ 0 by nlinarith]
    nlinarith
  have hE : prefixEval [1,3] lowerTau = (3 + Real.sqrt 3) / 6 := by
    dsimp [lowerTau, prefixEval]
    norm_num only [PNat.val_ofNat, Nat.cast_one, Nat.cast_ofNat]
    rw [h3]
    field_simp [show (1:ℝ) + (2 - Real.sqrt 3) ≠ 0 by nlinarith]
    nlinarith
  have h2 : (1:ℝ) / (2 + (3 + Real.sqrt 3) / 6) =
      (15 - Real.sqrt 3) / 37 := by
    field_simp [show (2:ℝ) + (3 + Real.sqrt 3) / 6 ≠ 0 by nlinarith]
    nlinarith
  have hF : prefixEval [1,2,1,3] lowerTau = (52 + Real.sqrt 3) / 73 := by
    dsimp [lowerTau, prefixEval]
    norm_num only [PNat.val_ofNat, Nat.cast_one, Nat.cast_ofNat]
    rw [h3]
    have he : (1:ℝ) / (1 + (2 - Real.sqrt 3)) = (3 + Real.sqrt 3) / 6 := by
      field_simp [show (1:ℝ) + (2 - Real.sqrt 3) ≠ 0 by nlinarith]
      nlinarith
    rw [he, h2]
    rw [div_eq_iff (show (1:ℝ) + (15 - Real.sqrt 3) / 37 ≠ 0 by nlinarith)]
    field_simp
    nlinarith
  rw [hE, hF]
  refine ⟨rfl, rfl, by nlinarith, ⟨by positivity, by nlinarith⟩,
    ⟨by positivity, by nlinarith⟩⟩

private theorem cd_append_one (w : List ℕ+) :
    lowerCD (w ++ [1]) = ((lowerCD w).2, (lowerCD w).1 + (lowerCD w).2) := by
  simp [lowerCD, List.foldl_append]

private theorem cd_append_two (w : List ℕ+) :
    lowerCD (w ++ [2]) = ((lowerCD w).2, (lowerCD w).1 + 2*(lowerCD w).2) := by
  simp [lowerCD, List.foldl_append]

private theorem cd_append_e (w : List ℕ+) :
    lowerCD (w ++ [1,3]) = ((lowerCD w).1 + (lowerCD w).2,
      3*(lowerCD w).1 + 4*(lowerCD w).2) := by
  simp [lowerCD, List.foldl_append]
  ring

private theorem endpoint_den_pos (w : List ℕ+) (z : ℝ) (hz : 0 ≤ z) :
    0 < ((lowerCD w).2 : ℝ) + z * (lowerCD w).1 := by
  have hq := q_pos w
  positivity

private theorem pe_signed_difference (w : List ℕ+) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    prefixEval w x - prefixEval w y =
      (x-y) * ((-1 : ℝ)^w.length) /
        ((((lowerCD w).2 : ℝ) + x*(lowerCD w).1) *
         (((lowerCD w).2 : ℝ) + y*(lowerCD w).1)) := by
  rw [prefixEval_mobius w x hx, prefixEval_mobius w y hy]
  have hc := cd_eq w
  have hd : (wordContinuantPrevP w : ℝ) * wordContinuantQ w -
      (wordContinuantP w : ℝ) * wordContinuantPrevQ w = (-1 : ℝ)^w.length := by
    exact_mod_cast continuant_determinant w
  have hqx : (wordContinuantQ w : ℝ) + x * wordContinuantPrevQ w ≠ 0 := by
    have hq : (0:ℝ) < wordContinuantQ w := by exact_mod_cast continuant_denominator_pos w
    positivity
  have hqy : (wordContinuantQ w : ℝ) + y * wordContinuantPrevQ w ≠ 0 := by
    have hq : (0:ℝ) < wordContinuantQ w := by exact_mod_cast continuant_denominator_pos w
    positivity
  rw [hc]
  dsimp only [Prod.fst, Prod.snd]
  rw [div_sub_div _ _ hqx hqy]
  congr 1
  linear_combination (x-y) * hd

private theorem pe_delta_abs (w : List ℕ+) :
    let E := prefixEval [1,3] lowerTau
    let F := prefixEval [1,2,1,3] lowerTau
    |prefixEval w E - prefixEval w F| =
      (E-F) / ((((lowerCD w).2:ℝ)+E*(lowerCD w).1) *
        (((lowerCD w).2:ℝ)+F*(lowerCD w).1)) := by
  dsimp only
  rw [prefixEval_difference w _ _ endpoint_tails.2.2.2.1 endpoint_tails.2.2.2.2]
  rw [abs_of_pos (sub_pos.mpr endpoint_tails.2.2.1), cd_eq]

end M7Ties15

namespace M7Ties15

private theorem algebra_classify {c d C D : ℝ}
    (hd : 0 < d) (hD : 0 < D) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hA : 4*c*d-3*c^2 = 4*C*D-3*C^2)
    (hB : 2*d^2-4*c*d+5*c^2 = 2*D^2-4*C*D+5*C^2) :
    (c = C ∧ d = D) ∨ (5*C = -3*c+4*d ∧ 5*D = 4*c+3*d) := by
  have hres : (c*D-C*d) * (4*c*C+3*c*D+3*C*d-4*d*D) = 0 := by
    have hz : (4*c*d-3*c^2)*(2*D^2-4*C*D+5*C^2) -
        (4*C*D-3*C^2)*(2*d^2-4*c*d+5*c^2) = 0 := by rw [hA,hB]; ring
    nlinarith [hz]
  rcases mul_eq_zero.mp hres with hcross | hfac
  · left
    have hid : (2*d^2-4*c*d+5*c^2)*D^2 -
        (2*D^2-4*C*D+5*C^2)*d^2 =
        (c*D-C*d)*(-4*d*D+5*c*D+5*C*d) := by ring
    rw [hcross] at hid
    have hsame : (2*D^2-4*C*D+5*C^2)*d^2 =
        (2*D^2-4*C*D+5*C^2)*D^2 := by nlinarith [hid]
    have hBp : 0 < 2*D^2-4*C*D+5*C^2 := by
      nlinarith [sq_pos_of_pos hD, sq_nonneg (D-2*C), sq_nonneg C]
    have hde : d = D := by nlinarith [hsame]
    have hce : c = C := by
      rw [hde] at hcross
      nlinarith
    exact ⟨hce,hde⟩
  · right
    have hcubic : D*(25*D^2-16*c^2-24*c*d-9*d^2) = 0 := by
      linear_combination (10*C-31/2*D)*hA + (6*C-25/2*D)*hB - 4*d*hfac
    have hsquare : (5*D)^2 = (4*c+3*d)^2 := by
      have hn : D ≠ 0 := ne_of_gt hD
      apply (mul_left_cancel₀ hn)
      nlinarith [hcubic]
    have hDe : 5*D = 4*c+3*d := by
      have hp : 0 < 4*c+3*d := by positivity
      nlinarith
    have hCe : 5*C = -3*c+4*d := by
      have hprod : D*(5*C+3*c-4*d) = 0 := by
        calc
          D*(5*C+3*c-4*d) = C*(5*D)+D*(3*c-4*d) := by ring
          _ = C*(4*c+3*d)+D*(3*c-4*d) := by rw [hDe]
          _ = 0 := by nlinarith [hfac]
      have := (mul_eq_zero.mp hprod).resolve_left (ne_of_gt hD)
      linarith
    exact ⟨hCe,hDe⟩

private theorem cd_classify (u v : List ℕ+) (hw : lowerWidth u = lowerWidth v) :
    lowerCD u = lowerCD v ∨
      (5*((lowerCD v).1:ℝ) = -3*((lowerCD u).1:ℝ)+4*(lowerCD u).2 ∧
       5*((lowerCD v).2:ℝ) = 4*((lowerCD u).1:ℝ)+3*(lowerCD u).2) := by
  have hh := M7TieWidth14.coefficients_of_width u v hw
  have hA : 4*((lowerCD u).1:ℝ)*(lowerCD u).2-3*((lowerCD u).1:ℝ)^2 =
      4*((lowerCD v).1:ℝ)*(lowerCD v).2-3*((lowerCD v).1:ℝ)^2 := by
    have h := hh.1
    dsimp [M7TieWidth14.coeffA] at h
    exact_mod_cast h
  have hB : 2*((lowerCD u).2:ℝ)^2-4*((lowerCD u).1:ℝ)*(lowerCD u).2+5*((lowerCD u).1:ℝ)^2 =
      2*((lowerCD v).2:ℝ)^2-4*((lowerCD v).1:ℝ)*(lowerCD v).2+5*((lowerCD v).1:ℝ)^2 := by
    have h := hh.2
    dsimp [M7TieWidth14.coeffB] at h
    exact_mod_cast h
  rcases algebra_classify (q_pos u) (q_pos v) (by positivity) (by positivity) hA hB with h | h
  · left
    apply Prod.ext
    · exact_mod_cast h.1
    · exact_mod_cast h.2
  · exact Or.inr h

end M7Ties15

namespace M7Ties15

private theorem cd_fst_le_snd (w : List ℕ+) : (lowerCD w).1 ≤ (lowerCD w).2 := by
  have hr := (lowerEarlyTerminal_ratio_range w).2
  rw [lowerRatio, div_le_one (q_pos w)] at hr
  exact_mod_cast hr

private theorem reflection_bounds {c d C D : ℝ}
    (hc : 0 ≤ c) (hcd : c ≤ d) (hdc : d ≤ 2*c)
    (hC : 5*C = -3*c+4*d) (hD : 5*D = 4*c+3*d) :
    let E := prefixEval [1,3] lowerTau
    let F := prefixEval [1,2,1,3] lowerTau
    let a := lowerAlpha
    let b := lowerBeta
    let ce := c+d
    let de := 3*c+4*d
    let Ce := C+D
    let De := 3*C+4*D
    (D+E*C)*(D+F*C) ≤ (d+E*c)*(d+F*c) ∧
      5*((De+a*Ce)*(De+b*Ce)) ≤ 7*((de+a*ce)*(de+b*ce)) ∧
      5*((de+a*ce)*(de+b*ce)) ≤ 7*((De+a*Ce)*(De+b*Ce)) := by
  dsimp only
  have hC' : C = (-3*c+4*d)/5 := by linarith
  have hD' : D = (4*c+3*d)/5 := by linarith
  have hs3 := radical3.1
  have hs30 := radical3.2.1
  have hs21 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 21)
  have hs210 := Real.sqrt_nonneg (21:ℝ)
  have hs21lo : 4 < Real.sqrt (21:ℝ) := by nlinarith
  have hdc0 : 0 ≤ 2*c-d := by linarith
  have hcp : 0 ≤ c+2*d := by linarith
  have hdcprod : 0 ≤ (2*c-d)*(c+2*d) := mul_nonneg hdc0 hcp
  rw [endpoint_tails.1, endpoint_tails.2.1, hC', hD']
  dsimp [lowerAlpha, lowerBeta]
  constructor
  · have hid :
        (d+(3+Real.sqrt 3)/6*c)*(d+(52+Real.sqrt 3)/73*c) -
          (((4*c+3*d)/5+(3+Real.sqrt 3)/6*((-3*c+4*d)/5))*
           ((4*c+3*d)/5+(52+Real.sqrt 3)/73*((-3*c+4*d)/5))) =
        ((477+457*Real.sqrt 3)/5475)*(c+2*d)*(2*c-d) := by
        field_simp
        nlinarith [hs3]
    have hk : 0 ≤ (477+457*Real.sqrt 3)/5475 := by nlinarith
    nlinarith [mul_nonneg hk hdcprod]
  constructor
  · have hq1 : 0 ≤ c*d-c^2 := by nlinarith [mul_nonneg hc (sub_nonneg.mpr hcd)]
    have hq2 : 0 ≤ d^2-c*d := by nlinarith [mul_nonneg (by linarith : 0 ≤ d) (sub_nonneg.mpr hcd)]
    have hsqc : 0 ≤ c^2 := sq_nonneg c
    have hsqD : 0 ≤ d^2 := sq_nonneg d
    have hsprod1 : 0 ≤ (Real.sqrt 21-4)*d^2 := mul_nonneg (by linarith) hsqD
    have hsprod2 : 0 ≤ (Real.sqrt 21-4)*(c*d) :=
      mul_nonneg (by linarith) (mul_nonneg hc (by linarith))
    have hsprod3 : 0 ≤ (5-Real.sqrt 21)*c^2 := by
      have hs5 : Real.sqrt (21:ℝ) < 5 := by nlinarith
      positivity
    field_simp
    nlinarith
  · have hsqc : 0 ≤ c^2 := sq_nonneg c
    have hcd0 : 0 ≤ c*d := mul_nonneg hc (by linarith)
    have hsqD : 0 ≤ d^2 := sq_nonneg d
    have h1 : 0 ≤ (Real.sqrt 21-4)*d^2 := mul_nonneg (by linarith) hsqD
    have hq1 : 0 ≤ c*d-c^2 := by nlinarith [mul_nonneg hc (sub_nonneg.mpr hcd)]
    have hq2 : 0 ≤ d^2-c*d := by nlinarith [mul_nonneg (by linarith : 0 ≤ d) (sub_nonneg.mpr hcd)]
    have hid :
        7*((3*((-3*c+4*d)/5)+4*((4*c+3*d)/5) + lowerAlpha*((-3*c+4*d)/5+(4*c+3*d)/5))*
           (3*((-3*c+4*d)/5)+4*((4*c+3*d)/5) + lowerBeta*((-3*c+4*d)/5+(4*c+3*d)/5))) -
        5*((3*c+4*d+lowerAlpha*(c+d))*(3*c+4*d+lowerBeta*(c+d))) =
        ((41*Real.sqrt 21+147)*d^2 - (19*Real.sqrt 21+51)*c^2 -
          (20*Real.sqrt 21+36)*c*d)/3 := by
      dsimp [lowerAlpha,lowerBeta]
      field_simp
      nlinarith [hs21]
    have ha : 0 ≤ (41*Real.sqrt 21+147)*(d^2-c*d) :=
      mul_nonneg (by positivity) hq2
    have hb : 0 ≤ (21*Real.sqrt 21+111)*(c*d-c^2) :=
      mul_nonneg (by positivity) hq1
    have hc0 : 0 ≤ (2*Real.sqrt 21+60)*c^2 := by positivity
    have hout : 0 ≤ ((41*Real.sqrt 21+147)*d^2 -
        (19*Real.sqrt 21+51)*c^2 - (20*Real.sqrt 21+36)*c*d)/3 := by
      have he : (41*Real.sqrt 21+147)*d^2 -
          (19*Real.sqrt 21+51)*c^2 - (20*Real.sqrt 21+36)*c*d =
          (41*Real.sqrt 21+147)*(d^2-c*d) +
          (21*Real.sqrt 21+111)*(c*d-c^2) +
          (2*Real.sqrt 21+60)*c^2 := by ring
      rw [he]
      positivity
    have hdiff : 0 ≤
        7*((3*((-3*c+4*d)/5)+4*((4*c+3*d)/5) + lowerAlpha*((-3*c+4*d)/5+(4*c+3*d)/5))*
           (3*((-3*c+4*d)/5)+4*((4*c+3*d)/5) + lowerBeta*((-3*c+4*d)/5+(4*c+3*d)/5))) -
        5*((3*c+4*d+lowerAlpha*(c+d))*(3*c+4*d+lowerBeta*(c+d))) := by
      rw [hid]
      exact hout
    exact sub_nonneg.mp hdiff

private theorem width_seven_fifths (u v : List ℕ+)
    (hden : 5*((((lowerCD v).1:ℝ)*lowerAlpha+(lowerCD v).2)*
        (((lowerCD v).1:ℝ)*lowerBeta+(lowerCD v).2)) ≤
      7*((((lowerCD u).1:ℝ)*lowerAlpha+(lowerCD u).2)*
        (((lowerCD u).1:ℝ)*lowerBeta+(lowerCD u).2))) :
    lowerWidth u ≤ (7/5:ℝ)*lowerWidth v := by
  rw [width_formula,width_formula]
  have hn := sub_pos.mpr tails.2.2
  have hu : 0 < ((((lowerCD u).1:ℝ)*lowerAlpha+(lowerCD u).2)*
      (((lowerCD u).1:ℝ)*lowerBeta+(lowerCD u).2)) := by
    have ha := tails.1.1
    have hb := tails.2.1.1
    have hq := q_pos u
    positivity
  have hv : 0 < ((((lowerCD v).1:ℝ)*lowerAlpha+(lowerCD v).2)*
      (((lowerCD v).1:ℝ)*lowerBeta+(lowerCD v).2)) := by
    have ha := tails.1.1
    have hb := tails.2.1.1
    have hq := q_pos v
    positivity
  rw [show (7/5:ℝ) * ((lowerBeta-lowerAlpha) /
      ((((lowerCD v).1:ℝ)*lowerAlpha+(lowerCD v).2)*
       (((lowerCD v).1:ℝ)*lowerBeta+(lowerCD v).2))) =
      ((7/5:ℝ)*(lowerBeta-lowerAlpha)) /
      ((((lowerCD v).1:ℝ)*lowerAlpha+(lowerCD v).2)*
       (((lowerCD v).1:ℝ)*lowerBeta+(lowerCD v).2)) by ring]
  rw [div_le_div_iff₀ hu hv]
  nlinarith [mul_pos hn hv]

private theorem tie_metric_data (P Q : List ℕ+)
    (hw : lowerWidth (P++[1]) = lowerWidth (Q++[2])) :
    let u := P++[1]
    let v := Q++[2]
    let E := prefixEval [1,3] lowerTau
    let F := prefixEval [1,2,1,3] lowerTau
    lowerWidth (u++[1,3]) ≤ (7/5:ℝ)*lowerWidth (v++[1,3]) ∧
    lowerWidth (v++[1,3]) ≤ (7/5:ℝ)*lowerWidth (u++[1,3]) ∧
    (((lowerCD v).2:ℝ)+E*(lowerCD v).1)*(((lowerCD v).2:ℝ)+F*(lowerCD v).1) ≤
      (((lowerCD u).2:ℝ)+E*(lowerCD u).1)*(((lowerCD u).2:ℝ)+F*(lowerCD u).1) := by
  dsimp only
  let u := P++[1]
  let v := Q++[2]
  have hcu := cd_append_one P
  have hcv := cd_append_two Q
  have huc : (0:ℝ) ≤ (lowerCD u).1 := by positivity
  have hucd : ((lowerCD u).1:ℝ) ≤ (lowerCD u).2 := by exact_mod_cast cd_fst_le_snd u
  have hudc : ((lowerCD u).2:ℝ) ≤ 2*(lowerCD u).1 := by
    rw [show lowerCD u = lowerCD (P++[1]) by rfl, hcu]
    push_cast
    have hp : (lowerCD P).1 ≤ (lowerCD P).2 := cd_fst_le_snd P
    have hpR : ((lowerCD P).1:ℝ) ≤ (lowerCD P).2 := by exact_mod_cast hp
    nlinarith
  rcases cd_classify u v hw with heq | href
  · have hae : lowerCD (u++[1,3]) = lowerCD (v++[1,3]) := by
      rw [cd_append_e,cd_append_e,heq]
    refine ⟨?_, ?_, ?_⟩
    · have hwe := width_eq_of_cd _ _ hae
      have hp := width_pos (v++[1,3])
      nlinarith
    · have hwe := width_eq_of_cd _ _ hae
      have hp := width_pos (u++[1,3])
      nlinarith
    · rw [heq]
  · have hb := reflection_bounds huc hucd hudc href.1 href.2
    refine ⟨?_, ?_, hb.1⟩
    · apply width_seven_fifths
      simpa only [cd_append_e, Prod.fst, Prod.snd, Nat.cast_add, Nat.cast_mul,
        Nat.cast_ofNat, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
        mul_assoc] using hb.2.1
    · apply width_seven_fifths
      simpa only [cd_append_e, Prod.fst, Prod.snd, Nat.cast_add, Nat.cast_mul,
        Nat.cast_ofNat, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
        mul_assoc] using hb.2.2

end M7Ties15

namespace M7Ties15

private theorem ends_one_not_three (P : List ℕ+) :
    ¬ lowerEnds (P++[1]) [3] := by
  simp [lowerEnds, ← List.reverse_prefix]

private theorem ends_two_not_three (P : List ℕ+) :
    ¬ lowerEnds (P++[2]) [3] := by
  simp [lowerEnds, ← List.reverse_prefix]

private theorem row1_words_lower (P Q : List ℕ+)
    (hp : P.length % 2 = 0) (hq : Q.length % 2 = 0)
    (hw : lowerWidth (P++[1]) = lowerWidth (Q++[2])) :
    lowerEndpointWords (P++[1],Q++[2]) false =
      (P++[1]++[1,3], Q++[2]++[1,2,1,3]) ∧
    lowerEndpointWords (Q++[2],P++[1]) false =
      (Q++[2]++[1,3], P++[1]++[1,2,1,3]) := by
  have hm := tie_metric_data P Q hw
  dsimp only at hm
  have hm1 : lowerWidth (P++[1,1,3]) ≤ (7/5:ℝ)*lowerWidth (Q++[2,1,3]) := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using hm.1
  have hm2 : lowerWidth (Q++[2,1,3]) ≤ (7/5:ℝ)*lowerWidth (P++[1,1,3]) := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using hm.2.1
  have hpo : (P.length+1)%2 = 1 := by omega
  have hqo : (Q.length+1)%2 = 1 := by omega
  constructor
  · unfold lowerEndpointWords
    have hpar : (P++[1]).length % 2 = (Q++[2]).length % 2 := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [if_pos hpar]
    unfold lowerEqualWords
    rw [show lowerNormalize (P++[1],Q++[2]) = (P++[1],Q++[2]) by
      simp [lowerNormalize, hw.ge]]
    simp [lowerNaturalShort, lowerEndpointSuffix, lowerEnds, ← List.reverse_prefix,
      hp, hq, hpo, hqo, hw.ge, hm1, List.append_assoc]
  · unfold lowerEndpointWords
    have hpar : (Q++[2]).length % 2 = (P++[1]).length % 2 := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [if_pos hpar]
    unfold lowerEqualWords
    rw [show lowerNormalize (Q++[2],P++[1]) = (Q++[2],P++[1]) by
      simp [lowerNormalize, hw.le]]
    simp [lowerNaturalShort, lowerEndpointSuffix, lowerEnds, ← List.reverse_prefix,
      hp, hq, hpo, hqo, hw.le, hm2, List.append_assoc]

private theorem row1_words_upper (P Q : List ℕ+)
    (hp : P.length % 2 = 1) (hq : Q.length % 2 = 1)
    (hw : lowerWidth (P++[1]) = lowerWidth (Q++[2])) :
    lowerEndpointWords (P++[1],Q++[2]) true =
      (P++[1]++[1,3], Q++[2]++[1,2,1,3]) ∧
    lowerEndpointWords (Q++[2],P++[1]) true =
      (Q++[2]++[1,3], P++[1]++[1,2,1,3]) := by
  have hm := tie_metric_data P Q hw
  dsimp only at hm
  have hm1 : lowerWidth (P++[1,1,3]) ≤ (7/5:ℝ)*lowerWidth (Q++[2,1,3]) := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using hm.1
  have hm2 : lowerWidth (Q++[2,1,3]) ≤ (7/5:ℝ)*lowerWidth (P++[1,1,3]) := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using hm.2.1
  have hpe : (P.length+1)%2 = 0 := by omega
  have hqe : (Q.length+1)%2 = 0 := by omega
  constructor
  · unfold lowerEndpointWords
    have hpar : (P++[1]).length % 2 = (Q++[2]).length % 2 := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [if_pos hpar]
    unfold lowerEqualWords
    rw [show lowerNormalize (P++[1],Q++[2]) = (P++[1],Q++[2]) by
      simp [lowerNormalize, hw.ge]]
    simp [lowerNaturalShort, lowerEndpointSuffix, lowerEnds, ← List.reverse_prefix,
      hp, hq, hpe, hqe, hw.ge, hm1, List.append_assoc]
  · unfold lowerEndpointWords
    have hpar : (Q++[2]).length % 2 = (P++[1]).length % 2 := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [if_pos hpar]
    unfold lowerEqualWords
    rw [show lowerNormalize (Q++[2],P++[1]) = (Q++[2],P++[1]) by
      simp [lowerNormalize, hw.le]]
    simp [lowerNaturalShort, lowerEndpointSuffix, lowerEnds, ← List.reverse_prefix,
      hp, hq, hpe, hqe, hw.le, hm2, List.append_assoc]

end M7Ties15

namespace M7Ties15

private theorem row1_delta_abs_le (P Q : List ℕ+)
    (hw : lowerWidth (P++[1]) = lowerWidth (Q++[2])) :
    let E := prefixEval [1,3] lowerTau
    let F := prefixEval [1,2,1,3] lowerTau
    |prefixEval (P++[1]) E - prefixEval (P++[1]) F| ≤
      |prefixEval (Q++[2]) E - prefixEval (Q++[2]) F| := by
  dsimp only
  have hm := (tie_metric_data P Q hw).2.2
  rw [pe_delta_abs, pe_delta_abs]
  apply div_le_div_of_nonneg_left (sub_nonneg.mpr endpoint_tails.2.2.1.le)
  · exact mul_pos (endpoint_den_pos _ _ endpoint_tails.2.2.2.1.1)
      (endpoint_den_pos _ _ endpoint_tails.2.2.2.2.1)
  · exact hm

private theorem delta_nonpos_of_odd (w : List ℕ+) (hp : w.length % 2 = 1) :
    prefixEval w (prefixEval [1,3] lowerTau) -
      prefixEval w (prefixEval [1,2,1,3] lowerTau) ≤ 0 := by
  rw [pe_signed_difference w _ _ endpoint_tails.2.2.2.1.1 endpoint_tails.2.2.2.2.1,
    neg_one_pow_eq_pow_mod_two, hp]
  norm_num only [pow_one]
  have hn := sub_pos.mpr endpoint_tails.2.2.1
  have hd := mul_pos (endpoint_den_pos w _ endpoint_tails.2.2.2.1.1)
    (endpoint_den_pos w _ endpoint_tails.2.2.2.2.1)
  exact (div_neg_of_neg_of_pos (by linarith) hd).le

private theorem delta_nonneg_of_even (w : List ℕ+) (hp : w.length % 2 = 0) :
    0 ≤ prefixEval w (prefixEval [1,3] lowerTau) -
      prefixEval w (prefixEval [1,2,1,3] lowerTau) := by
  rw [pe_signed_difference w _ _ endpoint_tails.2.2.2.1.1 endpoint_tails.2.2.2.2.1,
    neg_one_pow_eq_pow_mod_two, hp]
  norm_num only [pow_zero, mul_one]
  have hd := mul_pos (endpoint_den_pos w _ endpoint_tails.2.2.2.1.1)
    (endpoint_den_pos w _ endpoint_tails.2.2.2.2.1)
  exact div_nonneg (sub_nonneg.mpr endpoint_tails.2.2.1.le) hd.le

/-- The exact ordinary-width tie alignment needed by catalog row 1 in even base
parity. -/
private theorem row1_tie_lower (P Q : List ℕ+)
    (hp : P.length % 2 = 0) (hq : Q.length % 2 = 0)
    (hw : lowerWidth (P++[1]) = lowerWidth (Q++[2])) :
    lowerEndpoint (Q++[2],P++[1]) false ≤
      lowerEndpoint (P++[1],Q++[2]) false := by
  have hwords := row1_words_lower P Q hp hq hw
  have habs := row1_delta_abs_le P Q hw
  dsimp only at habs
  have hpu : (P++[1]).length % 2 = 1 := by
    simp only [List.length_append, List.length_cons,List.length_nil]
    omega
  have hqv : (Q++[2]).length % 2 = 1 := by
    simp only [List.length_append, List.length_cons,List.length_nil]
    omega
  have hsu := delta_nonpos_of_odd (P++[1]) hpu
  have hsv := delta_nonpos_of_odd (Q++[2]) hqv
  rw [abs_of_nonpos hsu, abs_of_nonpos hsv] at habs
  unfold lowerEndpoint
  rw [hwords.1,hwords.2]
  simp only [Prod.fst,Prod.snd]
  rw [pe_append (Q++[2]) [1,3], pe_append (P++[1]) [1,2,1,3],
    pe_append (P++[1]) [1,3], pe_append (Q++[2]) [1,2,1,3]]
  linarith

/-- The exact ordinary-width tie alignment needed by catalog row 1 in odd base
parity. -/
private theorem row1_tie_upper (P Q : List ℕ+)
    (hp : P.length % 2 = 1) (hq : Q.length % 2 = 1)
    (hw : lowerWidth (P++[1]) = lowerWidth (Q++[2])) :
    lowerEndpoint (P++[1],Q++[2]) true ≤
      lowerEndpoint (Q++[2],P++[1]) true := by
  have hwords := row1_words_upper P Q hp hq hw
  have habs := row1_delta_abs_le P Q hw
  dsimp only at habs
  have hpu : (P++[1]).length % 2 = 0 := by
    simp only [List.length_append, List.length_cons,List.length_nil]
    omega
  have hqv : (Q++[2]).length % 2 = 0 := by
    simp only [List.length_append, List.length_cons,List.length_nil]
    omega
  have hsu := delta_nonneg_of_even (P++[1]) hpu
  have hsv := delta_nonneg_of_even (Q++[2]) hqv
  rw [abs_of_nonneg hsu, abs_of_nonneg hsv] at habs
  unfold lowerEndpoint
  rw [hwords.1,hwords.2]
  simp only [Prod.fst,Prod.snd]
  rw [pe_append (P++[1]) [1,3], pe_append (Q++[2]) [1,2,1,3],
    pe_append (Q++[2]) [1,3], pe_append (P++[1]) [1,2,1,3]]
  linarith

end M7Ties15


namespace M7Ties15

/-- Catalog-row-1 tie containment in the exact conditional form consumed by the
history transfer proof. -/
private theorem row1_tie_alignment (P Q : List ℕ+)
    (hpar : P.length % 2 = Q.length % 2)
    (hw : lowerWidth (P++[1]) = lowerWidth (Q++[2])) :
    (if P.length % 2 = 0 then
      lowerEndpoint (Q++[2],P++[1]) false ≤ lowerEndpoint (P++[1],Q++[2]) false
    else
      lowerEndpoint (P++[1],Q++[2]) true ≤ lowerEndpoint (Q++[2],P++[1]) true) := by
  by_cases hp : P.length % 2 = 0
  · rw [if_pos hp]
    apply row1_tie_lower P Q hp
    · rw [← hpar]
      exact hp
    · exact hw
  · rw [if_neg hp]
    have hp1 : P.length % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one P.length with h | h
      · exact (hp h).elim
      · exact h
    have hq1 : Q.length % 2 = 1 := by rw [← hpar]; exact hp1
    exact row1_tie_upper P Q hp1 hq1 hw

end M7Ties15



open Freiman
namespace Mixed15

private theorem left_alignment (u v : List ℕ+) (hp : u.length % 2 = v.length % 2) :
    (if u.length % 2 = 0 then
      lowerEndpoint (v++[2],u++[1]) false ≤ lowerEndpoint (u++[1],v++[2]) false
    else lowerEndpoint (u++[1],v++[2]) true ≤ lowerEndpoint (v++[2],u++[1]) true) := by
  by_cases hw : lowerWidth (u++[1]) = lowerWidth (v++[2])
  · exact M7Ties15.row1_tie_alignment u v hp hw
  · have hpar : (u++[1]).length % 2 = (v++[2]).length % 2 := by
      simp only [List.length_append,List.length_singleton]
      omega
    have hn : LowerEarlyTerminalNoTies (u++[1],v++[2]) :=
      ⟨hw,fun h => (h hpar).elim⟩
    split_ifs
    · exact (lowerEarlyTerminal_endpoint_swap_nontie _ hn false).symm.le
    · exact (lowerEarlyTerminal_endpoint_swap_nontie _ hn true).le

end Mixed15


open Freiman
namespace CDUnique15

private theorem ratio_pos (w : List ℕ+) (hw : w ≠ []) : 0 < lowerRatio w := by
  unfold lowerRatio
  exact div_pos (by exact_mod_cast fst_pos w hw) (by exact_mod_cast snd_pos w)

private theorem ratio_two_lt_half (w : List ℕ+) (hw : w ≠ []) :
    lowerRatio (w ++ [2]) < (1 / 2 : ℝ) := by
  rw [lowerEarlyTerminal_ratio_append]
  change 1 / (2 + lowerRatio w) < 1 / 2
  have hr := ratio_pos w hw
  rw [div_lt_div_iff₀ (by linarith) (by norm_num)]
  linarith

private theorem width_ne_same_side_of_parity (u v : List ℕ+) (hu : GoodHead u)
    (hv : GoodHead v) (hp : u.length % 2 ≠ v.length % 2)
    (hside : ((1 / 2 : ℝ) < lowerRatio u ∧ (1 / 2 : ℝ) < lowerRatio v) ∨
      (lowerRatio u < (1 / 2 : ℝ) ∧ lowerRatio v < (1 / 2 : ℝ))) :
    lowerWidth u ≠ lowerWidth v := by
  intro hw
  have hcd := M7TieWidth14.cd_eq_of_width_same_side u v hw hside
  have heq := injective u v hu hv hcd
  exact hp (congrArg (fun w : List ℕ+ => w.length % 2) heq)

private theorem width_ne_append_two (u v : List ℕ+) (hu : GoodHead u) (hv : GoodHead v)
    (hnu : u ≠ []) (hnv : v ≠ []) (hp : u.length % 2 ≠ v.length % 2) :
    lowerWidth (u ++ [2]) ≠ lowerWidth (v ++ [2]) := by
  apply width_ne_same_side_of_parity _ _
    (goodHead_append _ _ hu hnu) (goodHead_append _ _ hv hnv)
  · simp only [List.length_append, List.length_singleton]
    omega
  · exact Or.inr ⟨ratio_two_lt_half u hnu, ratio_two_lt_half v hnv⟩

end CDUnique15


open Freiman
namespace Mixed15

-- This is an internal interface. Its proof is required before submitting the
-- original comparison-transfer theorem.
private def LowTieLaw : Prop :=
  ∀ (u v : List ℕ+), CDUnique15.GoodHead u → CDUnique15.GoodHead v →
    u ≠ [] → v ≠ [] → lowerEnds u [1] → lowerEnds v [2] →
    u.length % 2 = v.length % 2 → lowerWidth u = lowerWidth v →
    (if u.length % 2 = 0 then
      lowerEndpoint (u,v) false ≤ lowerEndpoint (v,u) false
    else lowerEndpoint (v,u) true ≤ lowerEndpoint (u,v) true)

private theorem alignment (hlow : LowTieLaw)
    (u v : List ℕ+) (hu : CDUnique15.GoodHead u) (hv : CDUnique15.GoodHead v)
    (hnu : u ≠ []) (hnv : v ≠ []) (hp : u.length % 2 ≠ v.length % 2) :
    (if v.length % 2 = 0 then
      lowerEndpoint (v++[2],u++[2]) false ≤ lowerEndpoint (u++[2],v++[2]) false
    else lowerEndpoint (u++[2],v++[2]) true ≤ lowerEndpoint (v++[2],u++[2]) true) := by
  classical
  let x := u ++ [2]
  let y := v ++ [2]
  have hxy : lowerWidth x ≠ lowerWidth y :=
    CDUnique15.width_ne_append_two u v hu hv hnu hnv hp
  have hxg : CDUnique15.GoodHead x := CDUnique15.goodHead_append _ _ hu hnu
  have hyg : CDUnique15.GoodHead y := CDUnique15.goodHead_append _ _ hv hnv
  have hy1g : CDUnique15.GoodHead (y++[1]) :=
    CDUnique15.goodHead_append _ _ hyg (by simp [y])
  rcases Nat.mod_two_eq_zero_or_one v.length with hve | hvo
  · rw [if_pos hve]
    change lowerEndpoint (y,x) false ≤ lowerEndpoint (x,y) false
    have hx : x.length % 2 = 0 := by simp only [x,List.length_append,List.length_singleton]; omega
    have hy : y.length % 2 = 1 := by simp only [y,List.length_append,List.length_singleton]; omega
    have hy1 : (y++[1]).length % 2 = 0 := by simp only [List.length_append,List.length_singleton]; omega
    have hpv : (y++[1]).length % 2 = x.length % 2 := hy1.trans hx.symm
    by_cases hwide : lowerWidth x ≤ lowerWidth y
    · have hnot : ¬ lowerWidth y ≤ lowerWidth x := fun h => hxy (le_antisymm hwide h)
      have he1 : lowerEndpoint (y,x) false = lowerEndpoint (y++[1],x) false := by
        simp [lowerEndpoint,lowerEndpointWords,hx,hy,hy1,hwide,hnot,List.length_append,Nat.add_mod]
      have he2 : lowerEndpoint (x,y) false = lowerEndpoint (x,y++[1]) false := by
        simp [lowerEndpoint,lowerEndpointWords,hx,hy,hy1,hwide,hnot,List.length_append,Nat.add_mod]
      rw [he1,he2]
      by_cases ht : lowerWidth (y++[1]) = lowerWidth x
      · have hh := hlow (y++[1]) x hy1g hxg (by simp) (by simp [x])
          ⟨y,rfl⟩ ⟨u,rfl⟩ hpv ht
        simpa only [hy1,if_true] using hh
      · have hn : LowerEarlyTerminalNoTies (y++[1],x) :=
          ⟨ht,fun h => (h hpv).elim⟩
        exact (lowerEarlyTerminal_endpoint_swap_nontie _ hn false).le
    · have hle : lowerWidth y ≤ lowerWidth x := (not_le.mp hwide).le
      apply le_of_eq
      simp [lowerEndpoint,lowerEndpointWords,lowerNaturalWords,hx,hy,hwide,hle]
      ring
  · rw [if_neg (by omega : ¬ v.length % 2 = 0)]
    change lowerEndpoint (x,y) true ≤ lowerEndpoint (y,x) true
    have hx : x.length % 2 = 1 := by simp only [x,List.length_append,List.length_singleton]; omega
    have hy : y.length % 2 = 0 := by simp only [y,List.length_append,List.length_singleton]; omega
    have hy1 : (y++[1]).length % 2 = 1 := by simp only [List.length_append,List.length_singleton]; omega
    have hpv : (y++[1]).length % 2 = x.length % 2 := hy1.trans hx.symm
    by_cases hwide : lowerWidth x ≤ lowerWidth y
    · have hnot : ¬ lowerWidth y ≤ lowerWidth x := fun h => hxy (le_antisymm hwide h)
      have he1 : lowerEndpoint (y,x) true = lowerEndpoint (y++[1],x) true := by
        simp [lowerEndpoint,lowerEndpointWords,hx,hy,hy1,hwide,hnot,List.length_append,Nat.add_mod]
      have he2 : lowerEndpoint (x,y) true = lowerEndpoint (x,y++[1]) true := by
        simp [lowerEndpoint,lowerEndpointWords,hx,hy,hy1,hwide,hnot,List.length_append,Nat.add_mod]
      rw [he1,he2]
      by_cases ht : lowerWidth (y++[1]) = lowerWidth x
      · have hh := hlow (y++[1]) x hy1g hxg (by simp) (by simp [x])
          ⟨y,rfl⟩ ⟨u,rfl⟩ hpv ht
        simpa only [hy1,show ¬ (1:ℕ)=0 by omega,if_false] using hh
      · have hn : LowerEarlyTerminalNoTies (y++[1],x) :=
          ⟨ht,fun h => (h hpv).elim⟩
        exact (lowerEarlyTerminal_endpoint_swap_nontie _ hn true).symm.le
    · have hle : lowerWidth y ≤ lowerWidth x := (not_le.mp hwide).le
      apply le_of_eq
      simp [lowerEndpoint,lowerEndpointWords,lowerNaturalWords,hx,hy,hwide,hle]
      ring

end Mixed15


open Freiman
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace M7LowTies15

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

private theorem width_formula (w : List ℕ+) :
    lowerWidth w = (lowerBeta - lowerAlpha) /
      ((((lowerCD w).1 : ℝ) * lowerAlpha + (lowerCD w).2) *
       (((lowerCD w).1 : ℝ) * lowerBeta + (lowerCD w).2)) := by
  unfold lowerWidth
  rw [prefixEval_difference w lowerBeta lowerAlpha tails.2.1 tails.1]
  rw [abs_of_pos (sub_pos.mpr tails.2.2), cd_eq]
  ring

private theorem width_pos (w : List ℕ+) : 0 < lowerWidth w := by
  rw [width_formula]
  have ha := tails.1.1
  have hb := tails.2.1.1
  have hq := q_pos w
  exact div_pos (sub_pos.mpr tails.2.2) (mul_pos (by positivity) (by positivity))

private theorem width_eq_of_cd (u v : List ℕ+) (h : lowerCD u = lowerCD v) :
    lowerWidth u = lowerWidth v := by rw [width_formula, width_formula, h]

private theorem pe_append : ∀ (u v : List ℕ+) (x : ℝ),
    prefixEval (u ++ v) x = prefixEval u (prefixEval v x)
  | [], _, _ => rfl
  | _ :: u, v, x => by simp only [List.cons_append, prefixEval, pe_append u v x]

private theorem radical3 :
    let s := Real.sqrt (3 : ℝ)
    s^2 = 3 ∧ 0 < s ∧ s < 2 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  dsimp
  refine ⟨hs, by nlinarith, by nlinarith⟩

private theorem endpoint_tails :
    let E := prefixEval [3] lowerTau
    let F := prefixEval [2,1,3] lowerTau
    E = 2 - Real.sqrt 3 ∧ F = (15 - Real.sqrt 3) / 37 ∧
      E < F ∧ E ∈ Set.Icc (0 : ℝ) 1 ∧ F ∈ Set.Icc (0 : ℝ) 1 := by
  have hs := radical3.1
  have hp := radical3.2.1
  have hh := radical3.2.2
  have hE : prefixEval [3] lowerTau = 2 - Real.sqrt 3 := by
    dsimp [lowerTau, prefixEval]
    norm_num only [PNat.val_ofNat, Nat.cast_ofNat]
    field_simp [show (3:ℝ) + (Real.sqrt 3 - 1) ≠ 0 by nlinarith]
    nlinarith
  have hF : prefixEval [2,1,3] lowerTau = (15 - Real.sqrt 3) / 37 := by
    dsimp [lowerTau, prefixEval]
    norm_num only [PNat.val_ofNat, Nat.cast_one, Nat.cast_ofNat]
    have h3 : (1:ℝ) / (3 + (Real.sqrt 3 - 1)) = 2 - Real.sqrt 3 := by
      field_simp [show (3:ℝ) + (Real.sqrt 3 - 1) ≠ 0 by nlinarith]
      nlinarith
    rw [h3]
    have h1 : (1:ℝ) / (1 + (2 - Real.sqrt 3)) = (3 + Real.sqrt 3) / 6 := by
      field_simp [show (1:ℝ) + (2 - Real.sqrt 3) ≠ 0 by nlinarith]
      nlinarith
    rw [h1]
    field_simp [show (2:ℝ) + (3 + Real.sqrt 3) / 6 ≠ 0 by nlinarith]
    nlinarith
  rw [hE,hF]
  refine ⟨rfl,rfl,by nlinarith,⟨by nlinarith,by nlinarith⟩,⟨by nlinarith,by nlinarith⟩⟩

private theorem cd_append_one (w : List ℕ+) :
    lowerCD (w ++ [1]) = ((lowerCD w).2, (lowerCD w).1 + (lowerCD w).2) := by
  simp [lowerCD, List.foldl_append]

private theorem cd_append_two (w : List ℕ+) :
    lowerCD (w ++ [2]) = ((lowerCD w).2, (lowerCD w).1 + 2*(lowerCD w).2) := by
  simp [lowerCD, List.foldl_append]

private theorem cd_append_low (w : List ℕ+) :
    lowerCD (w ++ [3]) = ((lowerCD w).2,
      (lowerCD w).1 + 3*(lowerCD w).2) := by
  simp [lowerCD, List.foldl_append]

private theorem endpoint_den_pos (w : List ℕ+) (z : ℝ) (hz : 0 ≤ z) :
    0 < ((lowerCD w).2 : ℝ) + z * (lowerCD w).1 := by
  have hq := q_pos w
  positivity

private theorem pe_signed_difference (w : List ℕ+) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    prefixEval w x - prefixEval w y =
      (x-y) * ((-1 : ℝ)^w.length) /
        ((((lowerCD w).2 : ℝ) + x*(lowerCD w).1) *
         (((lowerCD w).2 : ℝ) + y*(lowerCD w).1)) := by
  rw [prefixEval_mobius w x hx, prefixEval_mobius w y hy]
  have hc := cd_eq w
  have hd : (wordContinuantPrevP w : ℝ) * wordContinuantQ w -
      (wordContinuantP w : ℝ) * wordContinuantPrevQ w = (-1 : ℝ)^w.length := by
    exact_mod_cast continuant_determinant w
  have hqx : (wordContinuantQ w : ℝ) + x * wordContinuantPrevQ w ≠ 0 := by
    have hq : (0:ℝ) < wordContinuantQ w := by exact_mod_cast continuant_denominator_pos w
    positivity
  have hqy : (wordContinuantQ w : ℝ) + y * wordContinuantPrevQ w ≠ 0 := by
    have hq : (0:ℝ) < wordContinuantQ w := by exact_mod_cast continuant_denominator_pos w
    positivity
  rw [hc]
  dsimp only [Prod.fst, Prod.snd]
  rw [div_sub_div _ _ hqx hqy]
  congr 1
  linear_combination (x-y) * hd

private theorem pe_delta_abs (w : List ℕ+) :
    let E := prefixEval [3] lowerTau
    let F := prefixEval [2,1,3] lowerTau
    |prefixEval w E - prefixEval w F| =
      (F-E) / ((((lowerCD w).2:ℝ)+E*(lowerCD w).1) *
        (((lowerCD w).2:ℝ)+F*(lowerCD w).1)) := by
  dsimp only
  rw [prefixEval_difference w _ _ endpoint_tails.2.2.2.1 endpoint_tails.2.2.2.2]
  rw [abs_of_neg (sub_neg.mpr endpoint_tails.2.2.1), cd_eq]
  ring

end M7LowTies15

namespace M7LowTies15

private theorem algebra_classify {c d C D : ℝ}
    (hd : 0 < d) (hD : 0 < D) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hA : 4*c*d-3*c^2 = 4*C*D-3*C^2)
    (hB : 2*d^2-4*c*d+5*c^2 = 2*D^2-4*C*D+5*C^2) :
    (c = C ∧ d = D) ∨ (5*C = -3*c+4*d ∧ 5*D = 4*c+3*d) := by
  have hres : (c*D-C*d) * (4*c*C+3*c*D+3*C*d-4*d*D) = 0 := by
    have hz : (4*c*d-3*c^2)*(2*D^2-4*C*D+5*C^2) -
        (4*C*D-3*C^2)*(2*d^2-4*c*d+5*c^2) = 0 := by rw [hA,hB]; ring
    nlinarith [hz]
  rcases mul_eq_zero.mp hres with hcross | hfac
  · left
    have hid : (2*d^2-4*c*d+5*c^2)*D^2 -
        (2*D^2-4*C*D+5*C^2)*d^2 =
        (c*D-C*d)*(-4*d*D+5*c*D+5*C*d) := by ring
    rw [hcross] at hid
    have hsame : (2*D^2-4*C*D+5*C^2)*d^2 =
        (2*D^2-4*C*D+5*C^2)*D^2 := by nlinarith [hid]
    have hBp : 0 < 2*D^2-4*C*D+5*C^2 := by
      nlinarith [sq_pos_of_pos hD, sq_nonneg (D-2*C), sq_nonneg C]
    have hde : d = D := by nlinarith [hsame]
    have hce : c = C := by
      rw [hde] at hcross
      nlinarith
    exact ⟨hce,hde⟩
  · right
    have hcubic : D*(25*D^2-16*c^2-24*c*d-9*d^2) = 0 := by
      linear_combination (10*C-31/2*D)*hA + (6*C-25/2*D)*hB - 4*d*hfac
    have hsquare : (5*D)^2 = (4*c+3*d)^2 := by
      have hn : D ≠ 0 := ne_of_gt hD
      apply (mul_left_cancel₀ hn)
      nlinarith [hcubic]
    have hDe : 5*D = 4*c+3*d := by
      have hp : 0 < 4*c+3*d := by positivity
      nlinarith
    have hCe : 5*C = -3*c+4*d := by
      have hprod : D*(5*C+3*c-4*d) = 0 := by
        calc
          D*(5*C+3*c-4*d) = C*(5*D)+D*(3*c-4*d) := by ring
          _ = C*(4*c+3*d)+D*(3*c-4*d) := by rw [hDe]
          _ = 0 := by nlinarith [hfac]
      have := (mul_eq_zero.mp hprod).resolve_left (ne_of_gt hD)
      linarith
    exact ⟨hCe,hDe⟩

private theorem cd_classify (u v : List ℕ+) (hw : lowerWidth u = lowerWidth v) :
    lowerCD u = lowerCD v ∨
      (5*((lowerCD v).1:ℝ) = -3*((lowerCD u).1:ℝ)+4*(lowerCD u).2 ∧
       5*((lowerCD v).2:ℝ) = 4*((lowerCD u).1:ℝ)+3*(lowerCD u).2) := by
  have hh := M7TieWidth14.coefficients_of_width u v hw
  have hA : 4*((lowerCD u).1:ℝ)*(lowerCD u).2-3*((lowerCD u).1:ℝ)^2 =
      4*((lowerCD v).1:ℝ)*(lowerCD v).2-3*((lowerCD v).1:ℝ)^2 := by
    have h := hh.1
    dsimp [M7TieWidth14.coeffA] at h
    exact_mod_cast h
  have hB : 2*((lowerCD u).2:ℝ)^2-4*((lowerCD u).1:ℝ)*(lowerCD u).2+5*((lowerCD u).1:ℝ)^2 =
      2*((lowerCD v).2:ℝ)^2-4*((lowerCD v).1:ℝ)*(lowerCD v).2+5*((lowerCD v).1:ℝ)^2 := by
    have h := hh.2
    dsimp [M7TieWidth14.coeffB] at h
    exact_mod_cast h
  rcases algebra_classify (q_pos u) (q_pos v) (by positivity) (by positivity) hA hB with h | h
  · left
    apply Prod.ext
    · exact_mod_cast h.1
    · exact_mod_cast h.2
  · exact Or.inr h

end M7LowTies15

namespace M7LowTies15

private theorem cd_fst_le_snd (w : List ℕ+) : (lowerCD w).1 ≤ (lowerCD w).2 := by
  have hr := (lowerEarlyTerminal_ratio_range w).2
  rw [lowerRatio, div_le_one (q_pos w)] at hr
  exact_mod_cast hr

private theorem width_seven_fifths (u v : List ℕ+)
    (hden : 5*((((lowerCD v).1:ℝ)*lowerAlpha+(lowerCD v).2)*
        (((lowerCD v).1:ℝ)*lowerBeta+(lowerCD v).2)) ≤
      7*((((lowerCD u).1:ℝ)*lowerAlpha+(lowerCD u).2)*
        (((lowerCD u).1:ℝ)*lowerBeta+(lowerCD u).2))) :
    lowerWidth u ≤ (7/5:ℝ)*lowerWidth v := by
  rw [width_formula,width_formula]
  have hn := sub_pos.mpr tails.2.2
  have hu : 0 < ((((lowerCD u).1:ℝ)*lowerAlpha+(lowerCD u).2)*
      (((lowerCD u).1:ℝ)*lowerBeta+(lowerCD u).2)) := by
    have ha := tails.1.1
    have hb := tails.2.1.1
    have hq := q_pos u
    positivity
  have hv : 0 < ((((lowerCD v).1:ℝ)*lowerAlpha+(lowerCD v).2)*
      (((lowerCD v).1:ℝ)*lowerBeta+(lowerCD v).2)) := by
    have ha := tails.1.1
    have hb := tails.2.1.1
    have hq := q_pos v
    positivity
  rw [show (7/5:ℝ) * ((lowerBeta-lowerAlpha) /
      ((((lowerCD v).1:ℝ)*lowerAlpha+(lowerCD v).2)*
       (((lowerCD v).1:ℝ)*lowerBeta+(lowerCD v).2))) =
      ((7/5:ℝ)*(lowerBeta-lowerAlpha)) /
      ((((lowerCD v).1:ℝ)*lowerAlpha+(lowerCD v).2)*
       (((lowerCD v).1:ℝ)*lowerBeta+(lowerCD v).2)) by ring]
  rw [div_le_div_iff₀ hu hv]
  nlinarith [mul_pos hn hv]

private theorem reflection_bounds_low {c d C D : ℝ}
    (hc : 0 ≤ c) (hcd : c ≤ d) (hdc : d ≤ 2*c)
    (hC : 5*C = -3*c+4*d) (hD : 5*D = 4*c+3*d) :
    let E := prefixEval [3] lowerTau
    let F := prefixEval [2,1,3] lowerTau
    let a := lowerAlpha
    let b := lowerBeta
    let ce := d
    let de := c+3*d
    let Ce := D
    let De := C+3*D
    (d+E*c)*(d+F*c) ≤ (D+E*C)*(D+F*C) ∧
      5*((De+a*Ce)*(De+b*Ce)) ≤ 7*((de+a*ce)*(de+b*ce)) ∧
      5*((de+a*ce)*(de+b*ce)) ≤ 7*((De+a*Ce)*(De+b*Ce)) := by
  dsimp only
  have hC' : C = (-3*c+4*d)/5 := by linarith
  have hD' : D = (4*c+3*d)/5 := by linarith
  have hs3 := radical3.1
  have hs30 := radical3.2.1
  have hs21 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 21)
  have hs210 := Real.sqrt_nonneg (21:ℝ)
  have hs21lo : 4 < Real.sqrt (21:ℝ) := by nlinarith
  have hs21hi : Real.sqrt (21:ℝ) < 5 := by nlinarith
  have hprod : 0 ≤ (c+2*d)*(2*c-d) :=
    mul_nonneg (by linarith) (by linarith)
  rw [endpoint_tails.1, endpoint_tails.2.1, hC', hD']
  dsimp [lowerAlpha, lowerBeta]
  constructor
  · have hid :
      (((4*c+3*d)/5+(2-Real.sqrt 3)*((-3*c+4*d)/5))*
       ((4*c+3*d)/5+(15-Real.sqrt 3)/37*((-3*c+4*d)/5))) -
      ((d+(2-Real.sqrt 3)*c)*(d+(15-Real.sqrt 3)/37*c)) =
      (2*(182*Real.sqrt 3-251)/925)*(c+2*d)*(2*c-d) := by
      field_simp
      nlinarith [hs3]
    have hk : 0 ≤ 2*(182*Real.sqrt 3-251)/925 := by nlinarith
    nlinarith [mul_nonneg hk hprod]
  constructor
  · have hq1 : 0 ≤ c*d-c^2 := by
      nlinarith [mul_nonneg hc (sub_nonneg.mpr hcd)]
    have hq2 : 0 ≤ d^2-c*d := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ d) (sub_nonneg.mpr hcd)]
    have h1 : 0 ≤ (93*Real.sqrt 21+237)*(d^2-c*d) := by positivity
    have h2 : 0 ≤ (41*Real.sqrt 21+249)*(c*d-c^2) := by positivity
    have h3 : 0 ≤ (207-7*Real.sqrt 21)*c^2 :=
      mul_nonneg (by nlinarith) (sq_nonneg c)
    field_simp
    nlinarith
  · have hd0 : 0 ≤ d := by linarith
    have hgap : 0 ≤ (2*c-d)*d := mul_nonneg (by linarith) hd0
    have hk : 0 ≤ 111*Real.sqrt 21-321 := by nlinarith
    have h1 : 0 ≤ (111*Real.sqrt 21-321)*((2*c-d)*d) :=
      mul_nonneg hk hgap
    have h2 : 0 ≤ (382*Real.sqrt 21+1998)*(c*d) := by positivity
    have h3 : 0 ≤ (336*Real.sqrt 21+654)*c^2 := by positivity
    field_simp
    nlinarith

private theorem low_metric_data (u v : List ℕ+) (hu1 : lowerEnds u [1])
    (hw : lowerWidth u = lowerWidth v) :
    let E := prefixEval [3] lowerTau
    let F := prefixEval [2,1,3] lowerTau
    lowerWidth (u++[3]) ≤ (7/5:ℝ)*lowerWidth (v++[3]) ∧
    lowerWidth (v++[3]) ≤ (7/5:ℝ)*lowerWidth (u++[3]) ∧
    (((lowerCD u).2:ℝ)+E*(lowerCD u).1)*(((lowerCD u).2:ℝ)+F*(lowerCD u).1) ≤
      (((lowerCD v).2:ℝ)+E*(lowerCD v).1)*(((lowerCD v).2:ℝ)+F*(lowerCD v).1) := by
  dsimp only
  have huc : (0:ℝ) ≤ (lowerCD u).1 := by positivity
  have hucd : ((lowerCD u).1:ℝ) ≤ (lowerCD u).2 := by
    exact_mod_cast cd_fst_le_snd u
  obtain ⟨P,rfl⟩ := hu1
  have hudc : ((lowerCD (P++[1])).2:ℝ) ≤ 2*(lowerCD (P++[1])).1 := by
    rw [cd_append_one]
    push_cast
    have hp : (lowerCD P).1 ≤ (lowerCD P).2 := cd_fst_le_snd P
    have hpR : ((lowerCD P).1:ℝ) ≤ (lowerCD P).2 := by exact_mod_cast hp
    nlinarith
  rcases cd_classify (P++[1]) v hw with heq | href
  · have hae : lowerCD ((P++[1])++[3]) = lowerCD (v++[3]) := by
      rw [cd_append_low,cd_append_low,heq]
    refine ⟨?_, ?_, ?_⟩
    · have hwe := width_eq_of_cd _ _ hae
      nlinarith [width_pos (v++[3])]
    · have hwe := width_eq_of_cd _ _ hae
      nlinarith [width_pos ((P++[1])++[3])]
    · rw [heq]
  · have hb := reflection_bounds_low huc hucd hudc href.1 href.2
    refine ⟨?_, ?_, hb.1⟩
    · apply width_seven_fifths
      simpa only [cd_append_low, Prod.fst, Prod.snd, Nat.cast_add, Nat.cast_mul,
        Nat.cast_ofNat, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
        mul_assoc] using hb.2.1
    · apply width_seven_fifths
      simpa only [cd_append_low, Prod.fst, Prod.snd, Nat.cast_add, Nat.cast_mul,
        Nat.cast_ofNat, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
        mul_assoc] using hb.2.2

private theorem cd_append_three_one (w : List ℕ+) :
    lowerCD (w ++ [3,1]) =
      ((lowerCD w).1 + 3*(lowerCD w).2,
       (lowerCD w).1 + 4*(lowerCD w).2) := by
  simp [lowerCD, List.foldl_append]
  ring

private theorem low_not_short (u v : List ℕ+)
    (hu : CDUnique15.GoodHead u) (hv : CDUnique15.GoodHead v)
    (hu1 : lowerEnds u [1]) (hv2 : lowerEnds v [2])
    (hw : lowerWidth u = lowerWidth v) : ¬ lowerEnds u [3,1] := by
  rcases cd_classify u v hw with heq | href
  · have huv := CDUnique15.injective u v hu hv heq
    subst v
    have h1 := hu1.getLast (by simp)
    have h2 := hv2.getLast (by simp)
    have hx : (1 : ℕ+) = 2 := h1.trans h2.symm
    norm_num at hx
  · intro hu31
    obtain ⟨P,rfl⟩ := hu31
    obtain ⟨Q,rfl⟩ := hv2
    have hdu : 3*((lowerCD (P++[3,1])).2:ℝ) ≤
        4*(lowerCD (P++[3,1])).1 := by
      rw [cd_append_three_one]
      push_cast
      have hz : (0:ℝ) ≤ (lowerCD P).1 := by positivity
      nlinarith
    have hDv : ((lowerCD (Q++[2])).2:ℝ) ≤
        3*(lowerCD (Q++[2])).1 := by
      rw [cd_append_two]
      push_cast
      have hq := cd_fst_le_snd Q
      have hq' : ((lowerCD Q).1:ℝ) ≤ (lowerCD Q).2 := by exact_mod_cast hq
      nlinarith
    have hcpos : (0:ℝ) < (lowerCD (P++[3,1])).1 := by
      exact_mod_cast CDUnique15.fst_pos (P++[3,1]) (by simp)
    nlinarith [href.1, href.2]

private theorem low_words_lower (P Q : List ℕ+)
    (hp : (P++[1]).length % 2 = 0) (hq : (Q++[2]).length % 2 = 0)
    (hshort : ¬ lowerEnds (P++[1]) [3,1])
    (hw : lowerWidth (P++[1]) = lowerWidth (Q++[2])) :
    lowerEndpointWords (P++[1],Q++[2]) false =
      (P++[1]++[3], Q++[2]++[2,1,3]) ∧
    lowerEndpointWords (Q++[2],P++[1]) false =
      (Q++[2]++[3], P++[1]++[2,1,3]) := by
  have hm := low_metric_data (P++[1]) (Q++[2]) ⟨P,rfl⟩ hw
  dsimp only at hm
  have hp' : (P.length+1)%2 = 0 := by simpa using hp
  have hq' : (Q.length+1)%2 = 0 := by simpa using hq
  have hshort' : ¬ [3] <+: P.reverse := by
    simpa [lowerEnds, ← List.reverse_prefix] using hshort
  have hm1 : lowerWidth (P++[1,3]) ≤ (7/5:ℝ)*lowerWidth (Q++[2,3]) := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using hm.1
  have hm2 : lowerWidth (Q++[2,3]) ≤ (7/5:ℝ)*lowerWidth (P++[1,3]) := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using hm.2.1
  constructor
  · unfold lowerEndpointWords
    have hpar : (P++[1]).length % 2 = (Q++[2]).length % 2 := hp.trans hq.symm
    rw [if_pos hpar]
    unfold lowerEqualWords
    rw [show lowerNormalize (P++[1],Q++[2]) = (P++[1],Q++[2]) by
      simp [lowerNormalize, hw.ge]]
    simp [lowerNaturalShort, lowerEndpointSuffix, lowerEnds, ← List.reverse_prefix,
      hp', hq', hshort', hw.ge, hm1, List.append_assoc]
  · unfold lowerEndpointWords
    have hpar : (Q++[2]).length % 2 = (P++[1]).length % 2 := hq.trans hp.symm
    rw [if_pos hpar]
    unfold lowerEqualWords
    rw [show lowerNormalize (Q++[2],P++[1]) = (Q++[2],P++[1]) by
      simp [lowerNormalize, hw.le]]
    simp [lowerNaturalShort, lowerEndpointSuffix, lowerEnds, ← List.reverse_prefix,
      hp', hq', hshort', hw.le, hm2, List.append_assoc]

private theorem low_words_upper (P Q : List ℕ+)
    (hp : (P++[1]).length % 2 = 1) (hq : (Q++[2]).length % 2 = 1)
    (hshort : ¬ lowerEnds (P++[1]) [3,1])
    (hw : lowerWidth (P++[1]) = lowerWidth (Q++[2])) :
    lowerEndpointWords (P++[1],Q++[2]) true =
      (P++[1]++[3], Q++[2]++[2,1,3]) ∧
    lowerEndpointWords (Q++[2],P++[1]) true =
      (Q++[2]++[3], P++[1]++[2,1,3]) := by
  have hm := low_metric_data (P++[1]) (Q++[2]) ⟨P,rfl⟩ hw
  dsimp only at hm
  have hp' : (P.length+1)%2 = 1 := by simpa using hp
  have hq' : (Q.length+1)%2 = 1 := by simpa using hq
  have hshort' : ¬ [3] <+: P.reverse := by
    simpa [lowerEnds, ← List.reverse_prefix] using hshort
  have hm1 : lowerWidth (P++[1,3]) ≤ (7/5:ℝ)*lowerWidth (Q++[2,3]) := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using hm.1
  have hm2 : lowerWidth (Q++[2,3]) ≤ (7/5:ℝ)*lowerWidth (P++[1,3]) := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using hm.2.1
  constructor
  · unfold lowerEndpointWords
    have hpar : (P++[1]).length % 2 = (Q++[2]).length % 2 := hp.trans hq.symm
    rw [if_pos hpar]
    unfold lowerEqualWords
    rw [show lowerNormalize (P++[1],Q++[2]) = (P++[1],Q++[2]) by
      simp [lowerNormalize, hw.ge]]
    simp [lowerNaturalShort, lowerEndpointSuffix, lowerEnds, ← List.reverse_prefix,
      hp', hq', hshort', hw.ge, hm1, List.append_assoc]
  · unfold lowerEndpointWords
    have hpar : (Q++[2]).length % 2 = (P++[1]).length % 2 := hq.trans hp.symm
    rw [if_pos hpar]
    unfold lowerEqualWords
    rw [show lowerNormalize (Q++[2],P++[1]) = (Q++[2],P++[1]) by
      simp [lowerNormalize, hw.le]]
    simp [lowerNaturalShort, lowerEndpointSuffix, lowerEnds, ← List.reverse_prefix,
      hp', hq', hshort', hw.le, hm2, List.append_assoc]

private theorem low_delta_abs (u v : List ℕ+) (hu1 : lowerEnds u [1])
    (hw : lowerWidth u = lowerWidth v) :
    let E := prefixEval [3] lowerTau
    let F := prefixEval [2,1,3] lowerTau
    |prefixEval v E - prefixEval v F| ≤
      |prefixEval u E - prefixEval u F| := by
  dsimp only
  have hm := (low_metric_data u v hu1 hw).2.2
  rw [pe_delta_abs, pe_delta_abs]
  apply div_le_div_of_nonneg_left (sub_nonneg.mpr endpoint_tails.2.2.1.le)
  · exact mul_pos (endpoint_den_pos _ _ endpoint_tails.2.2.2.1.1)
      (endpoint_den_pos _ _ endpoint_tails.2.2.2.2.1)
  · exact hm

private theorem delta_nonpos_of_even (w : List ℕ+) (hp : w.length % 2 = 0) :
    prefixEval w (prefixEval [3] lowerTau) -
      prefixEval w (prefixEval [2,1,3] lowerTau) ≤ 0 := by
  rw [pe_signed_difference w _ _ endpoint_tails.2.2.2.1.1
    endpoint_tails.2.2.2.2.1, neg_one_pow_eq_pow_mod_two, hp]
  norm_num only [pow_zero, mul_one]
  have hd := mul_pos (endpoint_den_pos w _ endpoint_tails.2.2.2.1.1)
    (endpoint_den_pos w _ endpoint_tails.2.2.2.2.1)
  exact (div_neg_of_neg_of_pos (sub_neg.mpr endpoint_tails.2.2.1) hd).le

private theorem delta_nonneg_of_odd (w : List ℕ+) (hp : w.length % 2 = 1) :
    0 ≤ prefixEval w (prefixEval [3] lowerTau) -
      prefixEval w (prefixEval [2,1,3] lowerTau) := by
  rw [pe_signed_difference w _ _ endpoint_tails.2.2.2.1.1
    endpoint_tails.2.2.2.2.1, neg_one_pow_eq_pow_mod_two, hp]
  norm_num only [pow_one]
  have hn := sub_neg.mpr endpoint_tails.2.2.1
  have hd := mul_pos (endpoint_den_pos w _ endpoint_tails.2.2.2.1.1)
    (endpoint_den_pos w _ endpoint_tails.2.2.2.2.1)
  exact (div_nonneg (by linarith) hd.le)

private theorem lowTieLaw : Mixed15.LowTieLaw := by
  intro u v hu hv hnu hnv hu1 hv2 hpar hw
  have hshort := low_not_short u v hu hv hu1 hv2 hw
  have habs := low_delta_abs u v hu1 hw
  obtain ⟨P,rfl⟩ := hu1
  obtain ⟨Q,rfl⟩ := hv2
  dsimp only at habs
  rcases Nat.mod_two_eq_zero_or_one (P++[1]).length with hue | huo
  · have hve : (Q++[2]).length % 2 = 0 := hpar.symm ▸ hue
    rw [if_pos hue]
    have hwords := low_words_lower P Q hue hve hshort hw
    have hdu := delta_nonpos_of_even (P++[1]) hue
    have hdv := delta_nonpos_of_even (Q++[2]) hve
    rw [abs_of_nonpos hdv, abs_of_nonpos hdu] at habs
    unfold lowerEndpoint
    rw [hwords.1,hwords.2]
    simp only [Prod.fst,Prod.snd]
    rw [pe_append (P++[1]) [3] lowerTau,
      pe_append (Q++[2]) [2,1,3] lowerTau,
      pe_append (Q++[2]) [3] lowerTau,
      pe_append (P++[1]) [2,1,3] lowerTau]
    linarith
  · have hvo : (Q++[2]).length % 2 = 1 := hpar.symm ▸ huo
    simp only [if_neg (by omega : (P++[1]).length % 2 ≠ 0)]
    have hwords := low_words_upper P Q huo hvo hshort hw
    have hdu := delta_nonneg_of_odd (P++[1]) huo
    have hdv := delta_nonneg_of_odd (Q++[2]) hvo
    rw [abs_of_nonneg hdv, abs_of_nonneg hdu] at habs
    unfold lowerEndpoint
    rw [hwords.1,hwords.2]
    simp only [Prod.fst,Prod.snd]
    rw [pe_append (P++[1]) [3] lowerTau,
      pe_append (Q++[2]) [2,1,3] lowerTau,
      pe_append (Q++[2]) [3] lowerTau,
      pe_append (P++[1]) [2,1,3] lowerTau]
    linarith

end M7LowTies15



open Freiman

private theorem comparison_transfer_complete
    (hg : LowerHistoryGreaterLaw) (he : LowerHistoryEndpointLaw)
    (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n)
    (base : LowerPair) (p : LowerHistoryPath) (hp : lowerHistoryStructural p)
    (hr : lowerHistoryReached t h n base p) (hi : p.catalog ≠ .initial)
    (hrow : p.row ≠ 4) (ha : lowerHistoryEarlierAnchor base p t)
    (hc : lowerHistoryComparisonsHold p (lowerRatio base.1)
      (lowerRatio base.2) (lowerScale base)) :
    lowerHistoryTarget p.row (h n) t := by
  exact Transfer15.comparison_transfer_of_alignments
    (fun P1 P2 hpar _ _ _ _ => Mixed15.left_alignment P1 P2 hpar)
    (fun P1 P2 hpar hg1 hg2 hn1 hn2 =>
      Mixed15.alignment M7LowTies15.lowTieLaw P1 P2 hg1 hg2 hn1 hn2 hpar)
    hg he t h n hh base p hp hr hi hrow ha hc


theorem solution (hg : LowerHistoryGreaterLaw) (he : LowerHistoryEndpointLaw) (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n)
    (base : LowerPair) (p : LowerHistoryPath) (hp : lowerHistoryStructural p) (hr : lowerHistoryReached t h n base p) (hi : p.catalog ≠ .initial) (hrow : p.row ≠ 4)
    (ha : lowerHistoryEarlierAnchor base p t)
    (hc : lowerHistoryComparisonsHold p (lowerRatio base.1) (lowerRatio base.2) (lowerScale base)) :
    lowerHistoryTarget p.row (h n) t := by
  exact comparison_transfer_complete hg he t h n hh base p hp hr hi hrow ha hc

#print axioms solution
