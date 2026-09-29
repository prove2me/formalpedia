-- Prove2me | solution 1 for Freiman.lowerHistory_survivor_family
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-13T14:22:29.745523+00:00
-- url     : https://prove2.me/submissions/fc0ae8e4-5c6b-4e7e-ab48-201642f6d06e

import Definitions.Def_Freiman_lowerHistoryVerification
import Theorems.Thm_Freiman_lower_initial_family_normalization
import Mathlib.Tactic
open Freiman
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 0
set_option maxRecDepth 10000
private lemma suffix3_snoc (u : List ℕ+) (a : ℕ+) :
    ([3] : List ℕ+).IsSuffix (u ++ [a]) ↔ a = 3 := by
  simp [List.IsSuffix, eq_comm]
private lemma suffix33_snoc (u : List ℕ+) (a : ℕ+) :
    ([3,3] : List ℕ+).IsSuffix (u ++ [a]) ↔
      a = 3 ∧ ([3] : List ℕ+).IsSuffix u := by
  constructor
  · intro h
    obtain ⟨t,ht⟩ := h
    have hr := congrArg List.reverse ht
    simp only [List.reverse_append,List.reverse_cons,List.reverse_nil] at hr
    simp at hr
    rcases hr with ⟨ha,hu⟩
    subst a
    refine ⟨rfl,t,?_⟩
    have := congrArg List.reverse hu
    simpa using this
  · rintro ⟨rfl,t,rfl⟩
    exact ⟨t,by simp⟩
private lemma repeat_prefix_not3 (pre : List ℕ+) (n : ℕ)
    (hp : ¬ ([3] : List ℕ+).IsSuffix pre) :
    ¬ ([3] : List ℕ+).IsSuffix (pre ++ lowerRepeat lowerPeriod n) := by
  cases n with
  | zero => simpa [lowerRepeat] using hp
  | succ n =>
    rw [show lowerRepeat lowerPeriod (n+1) = lowerRepeat lowerPeriod n ++ lowerPeriod by
      simp [lowerRepeat,List.replicate_add,List.flatten_append]]
    rw [show pre ++ (lowerRepeat lowerPeriod n ++ lowerPeriod) =
      (pre ++ lowerRepeat lowerPeriod n ++ [3,1,3,1,2]) ++ [1] by
        simp [lowerPeriod,List.append_assoc]]
    rw [suffix3_snoc]
    norm_num
private theorem marked_no33 (f : LowerInitialFamily) (a k v : ℕ)
    (hm : (f = .A ∧ k = 0) ∨ (f = .B ∧ k = 0) ∨ (f = .C ∧ v = 0)) :
    ¬ lowerEnds (lowerNormalize (lowerFamilyPair f a k v)).1 [3,3] ∧
    ¬ lowerEnds (lowerNormalize (lowerFamilyPair f a k v)).2 [3,3] := by
  rcases hm with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · rw [lower_initial_family_normalization _ _ _ _ (by decide)]
    cases a <;> simp [lowerFamilyPair, lowerEnds, lowerRepeat, lowerPeriod,
      List.replicate_add,List.flatten_append,List.IsSuffix]
    all_goals constructor <;> intro x hx
    all_goals have hz := congrArg (fun z : List ℕ+ => z.reverse.tail.head?) hx
    all_goals simp at hz
  · rw [lower_initial_family_normalization _ _ _ _ (by decide)]
    simp [lowerFamilyPair, lowerEnds, List.IsSuffix]
    constructor <;> intro x hx
    all_goals have hz := congrArg (fun z : List ℕ+ => z.reverse.tail.head?) hx
    all_goals simp at hz
  · rw [lower_initial_family_normalization _ _ _ _ (by decide)]
    simp [lowerFamilyPair, lowerEnds, List.IsSuffix]
    constructor <;> intro x hx
    all_goals have hz := congrArg (fun z : List ℕ+ => z.reverse.tail.head?) hx
    all_goals simp at hz
private lemma suffix33_replicate (u : List ℕ+) (k : ℕ) :
    ([3,3] : List ℕ+).IsSuffix (u ++ List.replicate (k+2) 3) := by
  refine ⟨u ++ List.replicate k 3, ?_⟩
  simp [List.replicate_add,List.append_assoc]
private theorem family_restricted_of_no33 (f : LowerInitialFamily) (a k v : ℕ)
    (h1 : ¬ lowerEnds (lowerNormalize (lowerFamilyPair f a k v)).1 [3,3])
    (h2 : ¬ lowerEnds (lowerNormalize (lowerFamilyPair f a k v)).2 [3,3])
    (hna : f ≠ .auxB) :
    (f = .A ∧ k = 0) ∨ (f = .B ∧ k = 0) ∨ (f = .C ∧ v = 0) := by
  cases f with
  | A =>
    left; refine ⟨rfl,?_⟩
    by_contra hk
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    apply h1
    rw [lower_initial_family_normalization _ _ _ _ (by decide)]
    unfold lowerEnds
    convert suffix33_replicate ([4,3,2,2] ++ lowerRepeat lowerPeriod a) k using 1 <;>
      simp [lowerFamilyPair,Nat.add_assoc,List.append_assoc]
  | B =>
    right; left; refine ⟨rfl,?_⟩
    by_contra hk
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    apply h2
    rw [lower_initial_family_normalization _ _ _ _ (by decide)]
    unfold lowerEnds
    convert suffix33_replicate ([4,3,2,2] ++ lowerRepeat lowerPeriod a ++ [3,1]) k using 1 <;>
      simp [lowerFamilyPair,Nat.add_assoc,List.append_assoc]
  | C =>
    right; right; refine ⟨rfl,?_⟩
    by_contra hv
    obtain ⟨v,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hv
    apply h1
    rw [lower_initial_family_normalization _ _ _ _ (by decide)]
    unfold lowerEnds
    convert suffix33_replicate
        ([4,3,2,2] ++ lowerRepeat lowerPeriod a ++ [3,1] ++
          List.replicate (k+1) 3 ++ [2,1]) v using 1 <;>
      simp [lowerFamilyPair,Nat.add_assoc,List.append_assoc]
  | auxB => exact (hna rfl).elim
private lemma repeat_succ (n : ℕ) :
    lowerRepeat lowerPeriod (n+1) = lowerRepeat lowerPeriod n ++ lowerPeriod := by
  simp [lowerRepeat,List.replicate_add,List.flatten_append]
private theorem aux_not_marked (a k v : ℕ) (f : LowerInitialFamily) (b c d : ℕ)
    (hm : (f = .A ∧ c = 0) ∨ (f = .B ∧ c = 0) ∨ (f = .C ∧ d = 0)) :
    lowerNormalize (lowerFamilyPair .auxB a k v) ≠
      lowerNormalize (lowerFamilyPair f b c d) := by
  rcases hm with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · have hn := lower_initial_family_normalization .A b 0 d (by decide)
    rw [hn]
    simp only [reduceCtorEq,if_false]
    intro heq
    unfold lowerNormalize at heq
    split_ifs at heq
    all_goals unfold lowerFamilyPair at heq
    all_goals rw [repeat_succ] at heq
    all_goals dsimp only at heq
    all_goals have h1 := congrArg (fun z : LowerPair => z.1.reverse.take 3) heq
    all_goals have h2 := congrArg (fun z : LowerPair => z.2.reverse.take 3) heq
    all_goals simp [lowerPeriod,List.reverse_append] at h1 h2
  · have hn := lower_initial_family_normalization .B b 0 d (by decide)
    rw [hn]
    simp only [if_pos rfl]
    intro heq
    unfold lowerNormalize at heq
    split_ifs at heq
    all_goals unfold lowerFamilyPair at heq
    all_goals rw [repeat_succ] at heq
    all_goals dsimp only at heq
    all_goals have h1 := congrArg (fun z : LowerPair => z.1.reverse.take 3) heq
    all_goals have h2 := congrArg (fun z : LowerPair => z.2.reverse.take 3) heq
    all_goals simp [lowerFamilyPair,repeat_succ,lowerPeriod,List.reverse_append] at h1 h2
  · have hn := lower_initial_family_normalization .C b c 0 (by decide)
    rw [hn]
    simp only [reduceCtorEq,if_false]
    intro heq
    unfold lowerNormalize at heq
    split_ifs at heq
    all_goals unfold lowerFamilyPair at heq
    all_goals rw [repeat_succ] at heq
    all_goals dsimp only at heq
    all_goals have h1 := congrArg (fun z : LowerPair => z.1.reverse.take 3) heq
    all_goals have h2 := congrArg (fun z : LowerPair => z.2.reverse.take 3) heq
    all_goals simp [lowerPeriod,List.reverse_append] at h1 h2

private theorem marked_second3 (f : LowerInitialFamily) (a k v : ℕ)
    (hm : (f = .A ∧ k = 0) ∨ (f = .B ∧ k = 0) ∨ (f = .C ∧ v = 0)) :
    lowerEnds (lowerNormalize (lowerFamilyPair f a k v)).2 [3] := by
  rcases hm with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  all_goals rw [lower_initial_family_normalization _ _ _ _ (by decide)]
  · unfold lowerEnds
    convert (List.suffix_append
      ([3,2,1,1] ++ lowerRepeat lowerPeriod a ++ [3,1]) ([3] : List ℕ+)) using 1 <;>
      simp [lowerFamilyPair,List.append_assoc]
  · unfold lowerEnds
    convert (List.suffix_append
      ([4,3,2,2] ++ lowerRepeat lowerPeriod a ++ [3,1]) ([3] : List ℕ+)) using 1 <;>
      simp [lowerFamilyPair,List.append_assoc]
  · unfold lowerEnds
    convert (List.suffix_append
      ([3,2,1,1] ++ lowerRepeat lowerPeriod a ++ [3,1,3,1,2] ++
        List.replicate (k+1) 3 ++ [1]) ([3] : List ℕ+)) using 1 <;>
      simp [lowerFamilyPair,List.append_assoc]

private theorem marked_first_length (f : LowerInitialFamily) (a k v : ℕ)
    (hm : (f = .A ∧ k = 0) ∨ (f = .B ∧ k = 0) ∨ (f = .C ∧ v = 0)) :
    5 < (lowerNormalize (lowerFamilyPair f a k v)).1.length + 1 := by
  rcases hm with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  all_goals rw [lower_initial_family_normalization _ _ _ _ (by decide)]
  all_goals simp [lowerFamilyPair,lowerRepeat,lowerPeriod,List.length_flatten]
  all_goals omega

private theorem entry_is_one (base b : LowerPair) (l : LowerLabel)
    (hb3 : lowerEnds base.2 [3]) (hl : l ∈ lowerEntryLabels)
    (heq : (base.1++[1],base.2) = lowerChild b l) :
    l = (([1],[]) : LowerLabel) ∧ lowerNormalize b = base := by
  obtain ⟨r,hr⟩ := hb3
  rw [← hr] at heq
  simp only [lowerEntryLabels,List.mem_cons,List.not_mem_nil,or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · simp only [lowerChild,List.reverse_cons,List.reverse_nil,List.nil_append,
        List.append_nil] at heq
      have he := Prod.mk.inj heq
      apply Prod.ext
      · exact (List.append_cancel_right he.1).symm
      · exact he.2.symm.trans hr
  all_goals
    simp only [lowerChild,List.reverse_cons,List.reverse_nil,List.nil_append,
      List.append_nil] at heq
  all_goals have he := Prod.mk.inj heq
  · have hz := congrArg (fun z : List ℕ+ => z.reverse.head?) he.2
    simp at hz
  · have hz := congrArg (fun z : List ℕ+ => z.reverse.head?) he.2
    simp at hz
  · have hz := congrArg (fun z : List ℕ+ => z.reverse.head?) he.2
    simp at hz
  · have hz := congrArg (fun z : List ℕ+ => z.reverse.head?) he.1
    simp at hz
  · have hz := congrArg (fun z : List ℕ+ => z.reverse.head?) he.2
    simp at hz

private theorem fixed_length_le (r : LowerPair) (hr : r ∈ lowerFixedRoots) :
    r.1.length ≤ 5 := by
  simp [lowerFixedRoots] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

private theorem fixed_not_child (base r : LowerPair)
    (hlen : 5 < base.1.length + 1) (hr : r ∈ lowerFixedRoots) :
    (base.1++[1],base.2) ≠ r := by
  intro heq
  have he := congrArg (fun z : LowerPair => z.1.length) heq
  simp only [List.length_append,List.length_singleton] at he
  have := fixed_length_le r hr
  omega

private theorem bridge_not_child (base : LowerPair) (f : LowerInitialFamily)
    (a v : ℕ) (d : LowerPair) (hb3 : lowerEnds base.2 [3])
    (hd : d ∈ lowerBridgeLabels f a) :
    (base.1 ++ [1], base.2) ≠ lowerPhysicalAdd (lowerFamilyPair f a 0 v) d := by
  obtain ⟨r,hr⟩ := hb3
  intro heq
  rw [← hr] at heq
  have he := Prod.mk.inj heq
  cases f <;> simp only [lowerBridgeLabels] at hd
  · split_ifs at hd <;> simp only [List.mem_cons,List.not_mem_nil,or_false] at hd
    · rcases hd with rfl | rfl | rfl | rfl | rfl
      all_goals
        have hz := congrArg (fun z : List ℕ+ => z.reverse.head?) he.1
        simp at hz
    · rcases hd with rfl | rfl | rfl | rfl
      · have hz := congrArg (fun z : List ℕ+ => z.reverse.head?) he.1
        simp at hz
      · have hz := congrArg (fun z : List ℕ+ => z.reverse.head?) he.2
        simp at hz
      · have hz := congrArg (fun z : List ℕ+ => z.reverse.head?) he.1
        simp at hz
      · have hz := congrArg (fun z : List ℕ+ => z.reverse.head?) he.1
        simp at hz
  · simp only [List.mem_singleton] at hd
    subst d
    have hz := congrArg (fun z : List ℕ+ => z.reverse.head?) he.1
    simp at hz
  · exact (List.not_mem_nil hd).elim
  · exact (List.not_mem_nil hd).elim

private theorem recover_safe (t : ℝ) (base : LowerPair)
    (sf : LowerInitialFamily) (sa sk sv : ℕ)
    (sm : (sf = .A ∧ sk = 0) ∨ (sf = .B ∧ sk = 0) ∨ (sf = .C ∧ sv = 0))
    (hbase : base = lowerNormalize (lowerFamilyPair sf sa sk sv))
    (hroot : lowerInitialRoot t (base.1 ++ [1], base.2)) :
    ∃ (f : LowerInitialFamily) (a k v : ℕ),
      ((f = .A ∧ k = 0) ∨ (f = .B ∧ k = 0) ∨ (f = .C ∧ v = 0)) ∧
      lowerInitialSafeBound t f a k v ∧
      lowerNormalize (lowerFamilyPair f a k v) = base := by
  rcases hroot with hfixed | ⟨f,a,k,v,hselected,hordinary | hbridge⟩
  · have hlen : 5 < base.1.length + 1 := by
      rw [hbase]
      exact marked_first_length sf sa sk sv sm
    exact (fixed_not_child base _ hlen hfixed rfl).elim
  · rcases hordinary with ⟨l,hl,hchild,hsafe⟩
    have hone := entry_is_one base (lowerFamilyPair f a k v) l
      (by rw [hbase]; exact marked_second3 sf sa sk sv sm) hl hchild
    have hna : f ≠ .auxB := by
      intro hf
      subst f
      exact aux_not_marked a k v sf sa sk sv sm (hone.2.trans hbase)
    have hn := marked_no33 sf sa sk sv sm
    have hn1 : ¬ lowerEnds (lowerNormalize (lowerFamilyPair f a k v)).1 [3,3] := by
      rw [hone.2,hbase]
      exact hn.1
    have hn2 : ¬ lowerEnds (lowerNormalize (lowerFamilyPair f a k v)).2 [3,3] := by
      rw [hone.2,hbase]
      exact hn.2
    exact ⟨f,a,k,v,family_restricted_of_no33 f a k v hn1 hn2 hna,hsafe,hone.2⟩
  · rcases hbridge with ⟨rfl,d,hd,hchild⟩
    exact (bridge_not_child base f a v d
      (by rw [hbase]; exact marked_second3 sf sa sk sv sm) hd hchild).elim

theorem solution (t : ℝ) (h : ℕ → LowerPair) (n : ℕ)
    (hh : lowerHistory t h n) (base : LowerPair) (p : LowerHistoryPath)
    (hp : lowerHistoryStructural p) (hr : lowerHistoryReached t h n base p)
    (hs : lowerHistorySurvivor p) :
    ∃ (f : LowerInitialFamily) (a k v : ℕ),
      ((f = .A ∧ k = 0) ∨ (f = .B ∧ k = 0) ∨ (f = .C ∧ v = 0)) ∧
      lowerInitialSafeBound t f a k v ∧ lowerNormalize (h n) =
        ((lowerNormalize (lowerFamilyPair f a k v)).1++[1],
         (lowerNormalize (lowerFamilyPair f a k v)).2++[1]) := by
  rcases hs with ⟨hcat,hids,hrow,hctx,hentry,hiw,hsteps,hfw⟩
  rcases hr with ⟨start,flip,hsum,hreal,hbirth⟩
  rw [if_pos hcat] at hbirth
  rcases hbirth with ⟨hstart,sf,sa,sk,sv,sm,hselected,hbase,hzero⟩
  have hz : h 0 = (base.1 ++ [1],base.2) := by
    rw [hzero,hentry]
    simp only [lowerChild,List.reverse_cons,List.reverse_nil,List.nil_append,List.append_nil]
    rw [← hbase]
  have hroot : lowerInitialRoot t (base.1 ++ [1],base.2) := by
    rw [← hz]
    exact hh.1
  rcases recover_safe t base sf sa sk sv sm hbase hroot with
    ⟨f,a,k,v,hm,hsafe,hfamily⟩
  refine ⟨f,a,k,v,hm,hsafe,?_⟩
  have hn : n = 1 := by
    rw [hsteps] at hsum
    simp only [List.length_cons,List.length_nil] at hsum
    omega
  have hlast := (hreal.2.2.2 1 (by rw [hsteps]; simp)).2.2
  rw [hn]
  rw [hstart] at hlast
  simp only [Nat.zero_add] at hlast
  simp [lowerHistoryReplay,hentry,hiw,hsteps,lowerHistoryRawStep,
    lowerHistoryOrient] at hlast
  rw [hfamily]
  exact hlast

#print axioms solution
