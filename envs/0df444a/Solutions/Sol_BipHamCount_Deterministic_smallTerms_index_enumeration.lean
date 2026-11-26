-- Prove2me | solution 1 for BipHamCount.Deterministic.smallTerms_index_enumeration
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T10:16:22.848691+00:00
-- url     : https://prove2.me/submissions/75357bf2-8f79-4ce8-870f-c2dc8cc3eb8d

import Mathlib.Data.List.Sublists
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
import Definitions.Def_BipHamCount_Deterministic_Programs
open scoped BigOperators


open CapacitatedAssort.General
namespace BipHamCount.Deterministic
private def insertLoop {m : ℕ} (i : Fin m) (xs acc : List (Finset (Fin m))) : Work (List (Finset (Fin m))) := do
  let mut out := acc
  for x in xs do
    charge (m+3)
    out := insert i x :: out
  return out

private theorem insertLoop_run {m : ℕ} (i : Fin m) (xs acc : List (Finset (Fin m))) (s : ℕ) :
    (insertLoop i xs acc).run s = ((xs.map (insert i)).reverse ++ acc, s + (m+3)*xs.length) := by
  induction xs generalizing acc s with
  | nil => change (acc,s) = _; simp
  | cons x xs ih =>
    have eqn : (insertLoop i (x::xs) acc).run s =
        (insertLoop i xs (insert i x :: acc)).run (s+(m+3)) := by
      simp [insertLoop, charge, StateT.run_bind]
    rw [eqn,ih]
    simp [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem chooseSets_spec {m : ℕ} (xs : List (Fin m)) (q s : ℕ) :
    ((chooseSets xs q).run s).1.Perm ((xs.sublistsLen q).map List.toFinset) ∧
    ((chooseSets xs q).run s).2 ≤ s + (m+4)*(3*(xs.length+1)*(xs.length.choose q)+1) := by
  induction xs generalizing s q with
  | nil =>
    cases q with
    | zero => change [∅].Perm _ ∧ s+2 ≤ _; simp; omega
    | succ q => change [].Perm _ ∧ s+1 ≤ _; simp
  | cons i xs ih =>
    cases q with
    | zero => change [∅].Perm _ ∧ s+2 ≤ _; simp; nlinarith
    | succ q =>
      by_cases h : xs.length < q
      · have e : (chooseSets (i::xs) (q+1)).run s = ([],s+(m+4)) := by
          simp [chooseSets, h, charge, StateT.run_bind]; rfl
        have hn : (i::xs).length < q+1 := by simpa
        rw [e, List.sublistsLen_of_length_lt hn, Nat.choose_eq_zero_of_lt hn]; simp
      · let a := (chooseSets xs q).run (s+(m+4))
        let b := (chooseSets xs (q+1)).run a.2
        have e : (chooseSets (i::xs) (q+1)).run s =
            (insertLoop i a.1 b.1).run b.2 := by
          simp [chooseSets, h, insertLoop, a, b, charge, StateT.run_bind]; rfl
        obtain ⟨ha,hat⟩ := ih q (s+(m+4))
        change a.1.Perm _ at ha
        change a.2 ≤ _ at hat
        obtain ⟨hb,hbt⟩ := ih (q+1) a.2
        change b.1.Perm _ at hb
        change b.2 ≤ _ at hbt
        rw [e,insertLoop_run]
        simp only [List.length_cons, Nat.choose_succ_succ, List.sublistsLen_succ_cons,
          List.map_append, List.map_map, Prod.fst, Prod.snd]
        constructor
        · apply List.perm_append_comm.trans
          apply hb.append
          have hh := ((List.reverse_perm _).trans (ha.map (insert i)))
          simpa [List.map_map,Function.comp_def] using hh
        · have hlen : a.1.length = xs.length.choose q := by simpa using ha.length_eq
          rw [hlen]
          have hpos := Nat.choose_pos (Nat.le_of_not_gt h)
          nlinarith [Nat.mul_le_mul_left (m+4) (show 1 ≤ xs.length.choose q from hpos)]
end BipHamCount.Deterministic

open CapacitatedAssort.General
namespace BipHamCount.Deterministic
private abbrev Pair (m : ℕ) := Finset (Fin m) × Finset (Fin m)
private def three {m : ℕ} (i : Fin m) (p : Pair m) : List (Pair m) :=
  [(insert i p.1,p.2),(p.1,insert i p.2),(insert i p.1,insert i p.2)]

private def strip {m : ℕ} (i : Fin m) (p : Pair m) : Pair m := (p.1.erase i,p.2.erase i)

private def labelLoop {m : ℕ} (i : Fin m) (pairs acc : List (Pair m)) : Work (List (Pair m)) := do
  let mut out := acc
  for p in pairs do
    charge (4*(m+1)+4)
    let x := insert i p.1
    let y := insert i p.2
    out := (x,p.2) :: (p.1,y) :: (x,y) :: out
  return out

private lemma labelLoop_val {m : ℕ} (i : Fin m) (pairs acc : List (Pair m)) (s : ℕ) :
    ((labelLoop i pairs acc).run s).1 = pairs.reverse.flatMap (three i) ++ acc := by
  induction pairs generalizing acc s with
  | nil => rfl
  | cons p ps ih =>
    let next := three i p ++ acc
    have hstep : (labelLoop i (p::ps) acc).run s =
        (labelLoop i ps next).run (s + (4*(m+1)+4)) := by
      simp [labelLoop, charge, next, three, StateT.run_bind]
    rw [hstep,ih]
    simp [next, List.flatMap_append, List.append_assoc]

private theorem strip_of_mem {m : ℕ} {i : Fin m} {p t : Pair m}
    (hp : i ∉ p.1 ∪ p.2) (ht : t ∈ three i p) : strip i t = p := by
  obtain ⟨ha,hb⟩ : i ∉ p.1 ∧ i ∉ p.2 := by simpa using hp
  simp only [three, List.mem_cons,List.not_mem_nil, or_false] at ht
  rcases ht with rfl|rfl|rfl <;> simp [strip, ha,hb]

private theorem three_nodup {m : ℕ} {i : Fin m} {p : Pair m} (hp : i ∉ p.1 ∪ p.2) :
    (three i p).Nodup := by
  obtain ⟨ha,hb⟩ : i ∉ p.1 ∧ i ∉ p.2 := by simpa using hp
  have ha' : insert i p.1 ≠ p.1 := fun h => ha (h ▸ Finset.mem_insert_self i p.1)
  have hb' : insert i p.2 ≠ p.2 := fun h => hb (h ▸ Finset.mem_insert_self i p.2)
  simp [three,Prod.ext_iff,ha',hb',Ne.symm ha',Ne.symm hb']

private lemma mem_from_strip {m : ℕ} (i : Fin m) (t : Pair m) (h : i ∈ t.1 ∪ t.2) :
    t ∈ three i (strip i t) := by
  rcases t with ⟨a,b⟩
  by_cases ha : i ∈ a <;> by_cases hb : i ∈ b <;>
    simp_all [three,strip,Finset.erase_eq_of_notMem,Finset.insert_erase]

/-- Three-way labelling enumerates each ordered pair with the prescribed union once. -/
theorem labelPairs_spec {m : ℕ} (xs : List (Fin m)) (hn : xs.Nodup) (s : ℕ) :
    ((labelPairs xs).run s).1.Nodup ∧
    ∀ t : Finset (Fin m) × Finset (Fin m), t ∈ ((labelPairs xs).run s).1 ↔ t.1 ∪ t.2 = xs.toFinset := by
  induction xs generalizing s with
  | nil =>
    change [(∅,∅)].Nodup ∧ ∀ t : Pair m, t ∈ [(∅,∅)] ↔ t.1 ∪ t.2 = ∅
    simp [Prod.ext_iff]
  | cons i xs ih =>
    let sub := (labelPairs xs).run (s+1)
    have ⟨hi,hn'⟩ := List.nodup_cons.mp hn
    have hnot : i ∉ xs.toFinset := by simpa using hi
    obtain ⟨hd,hm⟩ := ih hn' (s+1)
    change sub.1.Nodup at hd
    change ∀ t : Pair m, t ∈ sub.1 ↔ t.1 ∪ t.2 = xs.toFinset at hm
    have hp {p : Pair m} (h : p ∈ sub.1.reverse) : i ∉ p.1 ∪ p.2 := by
      rw [(hm p).mp (List.mem_reverse.mp h)]
      exact hnot
    have hb : (labelPairs (i::xs)).run s = (labelLoop i sub.1 []).run sub.2 := rfl
    rw [hb,labelLoop_val,List.append_nil]
    constructor
    · apply List.nodup_flatMap.mpr
      refine ⟨fun p h => three_nodup (hp h), ?_⟩
      apply List.Pairwise.imp_of_mem (l := sub.1.reverse) (R := (· ≠ ·)) _ (List.nodup_reverse.mpr hd)
      intro p q h₁ h₂ hpq
      apply List.disjoint_left.mpr
      intro t htp htq
      exact hpq ((strip_of_mem (hp h₁) htp).symm.trans (strip_of_mem (hp h₂) htq))
    · intro t
      rw [List.mem_flatMap, List.toFinset_cons]
      constructor
      · rintro ⟨p,hp',ht⟩
        have he := (hm p).mp (List.mem_reverse.mp hp')
        simp only [three,List.mem_cons,List.not_mem_nil, or_false] at ht
        rcases ht with rfl|rfl|rfl <;> simp [←he,Finset.insert_union,Finset.union_insert]
      · intro ht
        have hi' : i ∈ t.1 ∪ t.2 := ht ▸ Finset.mem_insert_self _ _
        refine ⟨strip i t, List.mem_reverse.mpr ((hm _).mpr ?_), mem_from_strip i t hi'⟩
        change t.1.erase i ∪ t.2.erase i = xs.toFinset
        have hu : t.1.erase i ∪ t.2.erase i = (t.1 ∪ t.2).erase i := by
          ext v; simp only [Finset.mem_union,Finset.mem_erase]; tauto
        rw [hu,ht,Finset.erase_insert hnot]
end BipHamCount.Deterministic


/-! Two runtime estimates for Proposition 4.2 of Prove2Me project 814.
The three-way labelling bound refers to the registered StateM program, with
its original charges. The binomial estimate uses the cutoff from the project. -/

open CapacitatedAssort.General
open scoped BigOperators
open Real Finset
namespace BipHamCount.Deterministic


private abbrev PairList (m : ℕ) := List (Finset (Fin m) × Finset (Fin m))

private def extendLabels {m : ℕ} (i : Fin m) (pairs acc : PairList m) : Work (PairList m) := do
  let mut out := acc
  for p in pairs do
    charge (4*(m+1)+4)
    let x := insert i p.1
    let y := insert i p.2
    out := (x,p.2) :: (p.1,y) :: (x,y) :: out
  return out

private theorem extendLabels_run {m : ℕ} (i : Fin m) (pairs acc : PairList m) (s : ℕ) :
    ((extendLabels i pairs acc).run s).1.length = 3*pairs.length + acc.length ∧
    ((extendLabels i pairs acc).run s).2 = s + (4*(m+1)+4)*pairs.length := by
  induction pairs generalizing acc s with
  | nil =>
    change acc.length = 3*0+acc.length ∧ s = s+(4*(m+1)+4)*0
    simp
  | cons p ps ih =>
    let next := (insert i p.1, p.2) :: (p.1, insert i p.2) :: (insert i p.1, insert i p.2) :: acc
    have hstep : (extendLabels i (p::ps) acc).run s =
        (extendLabels i ps next).run (s + (4*(m+1)+4)) := by
      simp [extendLabels, charge, next, StateT.run_bind]
    rw [hstep]
    obtain ⟨h₁,h₂⟩ := ih next (s + (4*(m+1)+4))
    simp only [h₁,h₂,List.length_cons]
    simp [next, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- The registered enumeration routine produces precisely 3^q entries on q indices.
Its charged work, starting with any counter s, is at most (4m+12)3^q. -/
theorem labelPairs_length_cost {m : ℕ} (xs : List (Fin m)) (s : ℕ) :
    ((labelPairs xs).run s).1.length = 3^xs.length ∧
    ((labelPairs xs).run s).2 ≤ s + (4*m+12)*3^xs.length := by
  induction xs generalizing s with
  | nil =>
    change 1 = 3^0 ∧ s+2 ≤ s+(4*m+12)*3^0
    simp
  | cons i xs ih =>
    let sub := (labelPairs xs).run (s+1)
    have hstep : (labelPairs (i::xs)).run s = (extendLabels i sub.1 []).run sub.2 := rfl
    rw [hstep]
    obtain ⟨hL,hC⟩ := extendLabels_run i sub.1 [] sub.2
    obtain ⟨hN,hS⟩ := ih (s+1)
    change sub.1.length = _ at hN
    change sub.2 ≤ _ at hS
    rw [hL,hC,hN]
    simp only [List.length_nil,add_zero,List.length_cons,pow_succ]
    constructor
    · exact Nat.mul_comm _ _
    · have hpos : 0 < 3 ^ xs.length := pow_pos (by decide) _
      nlinarith


/-- The number of pairs (X,Y) with union of size at most k, in the range used
by the small-term algorithm. Entropy uses natural logarithms. -/
theorem small_term_count_bound (m k : ℕ) (p : ℝ) (hp : 0 < p) (hp3 : p ≤ 3/4)
    (hk : (k : ℝ) ≤ p * m) :
    (∑ q ∈ range (k+1), (m.choose q : ℝ) * (3 : ℝ)^q) ≤
      exp ((m : ℝ) * binEntropy p) * (3 : ℝ)^(p*m) := by
  have hp1 : 0 < 1-p := by linarith
  let t : ℝ := p / (3*(1-p))
  have ht : 0 < t := div_pos hp (by positivity)
  have ht1 : t ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < 3*(1-p))).mpr
    linarith
  have hkm : k ≤ m := by
    exact_mod_cast hk.trans (by nlinarith [mul_nonneg (le_of_lt hp1) (Nat.cast_nonneg m)] : p*m ≤ m)
  have hsum : (∑ q ∈ range (k+1), (m.choose q : ℝ) * (3:ℝ)^q) * t^(p*m) ≤ (3*t+1)^m := by
    rw [Finset.sum_mul, add_pow]
    simp only [one_pow, mul_one]
    calc
      _ ≤ ∑ q ∈ range (k+1), (3*t)^q * (m.choose q : ℝ) := by
        apply sum_le_sum
        intro q hq
        have hqk : q ≤ k := Nat.le_of_lt_succ (mem_range.mp hq)
        have hpow := Real.rpow_le_rpow_of_exponent_ge ht ht1 ((Nat.cast_le.mpr hqk).trans hk)
        rw [Real.rpow_natCast] at hpow
        rw [mul_pow]
        calc
          _ ≤ (m.choose q : ℝ) * (3:ℝ)^q * t^q := by gcongr
          _ = _ := by ring
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (fun _ _ _ => by positivity)
  have htpos := Real.rpow_pos_of_pos ht (p*m)
  have hid : exp ((m:ℝ) * binEntropy p) * (3:ℝ)^(p*m) * t^(p*m) = (3*t+1)^m := by
    apply Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity))
    rw [Real.log_mul (by positivity) htpos.ne', Real.log_mul (by positivity) (by positivity),
      Real.log_exp, Real.log_rpow (by norm_num : (0:ℝ)<3), Real.log_rpow ht, Real.log_pow]
    have hbase : 3*t+1 = (1-p)⁻¹ := by dsimp [t]; field_simp; ring
    rw [hbase, Real.log_inv, show log t = log p - (log 3 + log (1-p)) by
      dsimp only [t]
      rw [Real.log_div hp.ne' (by positivity), Real.log_mul (by norm_num) hp1.ne']]
    simp only [Real.binEntropy, Real.log_inv]
    ring
  exact (le_of_mul_le_mul_right (hsum.trans_eq hid.symm) htpos)

/-- The bound instantiated at the cutoff used by smallTerms. -/
theorem smallTerms_enumeration_bound (m : ℕ) :
    (∑ q ∈ range (kOf m + 1), (m.choose q : ℝ) * (3:ℝ)^q) ≤
      exp ((m:ℝ) * binEntropy alpha) * (3:ℝ)^(alpha*m) := by
  unfold kOf alpha
  apply small_term_count_bound <;> try norm_num
  have h := Nat.div_mul_le_self (60909*m) 100000
  have hh : (↑(60909*m/100000) : ℝ) * 100000 ≤ 60909 * m := by exact_mod_cast h
  linarith

end BipHamCount.Deterministic

open BipHamCount.Deterministic
theorem solution :
    (∀ (m : ℕ) (xs : List (Fin m)) (q s : ℕ),
      ((chooseSets xs q).run s).1.Perm ((xs.sublistsLen q).map List.toFinset) ∧
      ((chooseSets xs q).run s).2 ≤ s + (m+4)*(3*(xs.length+1)*(xs.length.choose q)+1)) ∧
    (∀ (m : ℕ) (xs : List (Fin m)) (s : ℕ), xs.Nodup →
      ((labelPairs xs).run s).1.Nodup ∧
      (∀ t : Finset (Fin m) × Finset (Fin m),
        t ∈ ((labelPairs xs).run s).1 ↔ t.1 ∪ t.2 = xs.toFinset) ∧
      ((labelPairs xs).run s).1.length = 3^xs.length ∧
      ((labelPairs xs).run s).2 ≤ s+(4*m+12)*3^xs.length) ∧
    (∀ m : ℕ, (∑ q ∈ Finset.range (kOf m+1), (m.choose q : ℝ)*(3:ℝ)^q) ≤
      Real.exp ((m:ℝ)*Real.binEntropy alpha)*(3:ℝ)^(alpha*m)) := by
  refine ⟨fun _ xs q s => chooseSets_spec xs q s, ?_, smallTerms_enumeration_bound⟩
  intro m xs s h
  obtain ⟨hd,hm⟩ := labelPairs_spec xs h s
  exact ⟨hd,hm,labelPairs_length_cost xs s⟩
