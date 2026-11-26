-- Prove2me | solution 1 for BipHamCount.Deterministic.largeTerms_layer_enumeration
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T10:20:20.05181+00:00
-- url     : https://prove2.me/submissions/d6255999-b07b-4ebb-9151-22473c07feb3

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Interval.Finset.Fin
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
private def suffixLoop {m : ℕ} (lo : ℕ) (xs acc : List (Fin m)) : Work (List (Fin m)) := do
  let mut out := acc
  for i in xs do
    charge (m+3)
    if lo ≤ i.val then out := i::out
  return out

private theorem suffixLoop_run {m : ℕ} (lo : ℕ) (xs acc : List (Fin m)) (s : ℕ) :
    (suffixLoop lo xs acc).run s = ((xs.filter (fun i => decide (lo ≤ i.val))).reverse ++ acc,
      s+(m+3)*xs.length) := by
  induction xs generalizing acc s with
  | nil => change (acc,s) = _; simp
  | cons i xs ih =>
    by_cases hi : lo ≤ i.val
    · have h : (suffixLoop lo (i::xs) acc).run s = (suffixLoop lo xs (i::acc)).run (s+(m+3)) := by
        simp [suffixLoop,charge,StateT.run_bind,hi]
      rw [h,ih]; simp [hi,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    · have h : (suffixLoop lo (i::xs) acc).run s = (suffixLoop lo xs acc).run (s+(m+3)) := by
        simp [suffixLoop,charge,StateT.run_bind,hi]
      rw [h,ih]; simp [hi,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem suffix_run {m : ℕ} (lo s : ℕ) :
    (suffix (m := m) lo).run s = ((List.finRange m).filter (fun i => decide (lo ≤ i.val)),
      s+(4*m+1)+(m+3)*m) := by
  change (suffixLoop lo (List.finRange m).reverse []).run (s+(4*m+1)) = _
  rw [suffixLoop_run]
  simp [List.filter_reverse]
end BipHamCount.Deterministic
open CapacitatedAssort.General Finset
namespace BipHamCount.Deterministic

private theorem filtered_suffix_length (m lo : ℕ) :
    ((List.finRange m).filter (fun i => decide (lo ≤ i.val))).length=m-lo := by
  classical
  let xs := (List.finRange m).filter (fun i => decide (lo ≤ i.val))
  have hn : xs.Nodup := (List.nodup_finRange m).filter _
  change xs.length=_
  rw [←List.toFinset_card_of_nodup hn]
  by_cases hlo : lo < m
  · let v : Fin m := ⟨lo,hlo⟩
    have he : xs.toFinset=Finset.Ici v := by ext i; simp [xs,v,Fin.le_def]
    rw [he,Fin.card_Ici]
  · have he : xs.toFinset=∅ := by
      ext i
      have hi : ¬ (lo ≤ i.val) := by have := i.isLt; omega
      simp [xs,hi]
    rw [he]; simp; omega

theorem large_layer_count (m k q s₁ s₂ s₃ s₄ : ℕ) :
    ((chooseSets ((suffix (m:=m) (k-q)).run s₁).1 q).run s₂).1.length *
    ((chooseSets ((suffix (m:=m) 0).run s₃).1 q).run s₄).1.length =
      (m-(k-q)).choose q * m.choose q := by
  rw [suffix_run,suffix_run]
  simp only
  rw [(chooseSets_spec _ _ _).1.length_eq,(chooseSets_spec _ _ _).1.length_eq]
  simp only [List.length_map,List.length_sublistsLen,filtered_suffix_length,Nat.sub_zero]
end BipHamCount.Deterministic

open scoped BigOperators
open Real Finset

private theorem tilted_choose (a q : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (a.choose q : ℝ)*t^q ≤ (t+1)^a := by
  by_cases h : q ≤ a
  · rw [add_pow]
    simp only [one_pow, mul_one]
    rw [mul_comm]
    exact Finset.single_le_sum (f:=fun i => t^i*(a.choose i:ℝ)) (fun i _ => by positivity)
      (Finset.mem_range.mpr (by omega : q < a+1))
  · simp [Nat.choose_eq_zero_of_lt (by omega : a < q), (by positivity : 0 ≤ (t+1)^a)]

private theorem tilted_pairs (m k q : ℕ) (hk : k ≤ m) (t : ℝ)
    (ht : 1 ≤ t) (hs : t^2 ≤ t+1) :
    (m.choose q : ℝ)*((m-(k-q)).choose q : ℝ)*t^(2*k) ≤ (t+1)^(2*m) := by
  have ht0 : 0 ≤ t := by linarith
  let d := k-q
  let a := m-d
  have ham : a+d=m := by dsimp [a,d]; omega
  have hb := mul_le_mul (tilted_choose m q t ht0) (tilted_choose a q t ht0)
    (by positivity) (by positivity)
  change (m.choose q : ℝ)*(a.choose q:ℝ)*t^(2*k) ≤ _
  by_cases h : q ≤ k
  · have hd : d+q=k := by dsimp [d]; omega
    have he : (t^2)^d ≤ (t+1)^d := by gcongr
    calc
      _ = ((m.choose q : ℝ)*t^q*((a.choose q:ℝ)*t^q))*(t^2)^d := by
        rw [←hd, Nat.mul_add, pow_add, ←pow_mul, Nat.mul_comm 2 q, pow_mul]; ring
      _ ≤ ((t+1)^m*(t+1)^a)*(t+1)^d := by gcongr
      _ = _ := by rw [mul_assoc,←pow_add,ham,←pow_add, two_mul]
  · have ha : a=m := by dsimp [a,d]; omega
    rw [ha] at hb ⊢
    have hpow : t^(2*k) ≤ t^(2*q) := pow_le_pow_right₀ ht (by omega)
    calc
      _ ≤ (m.choose q:ℝ)*(m.choose q:ℝ)*t^(2*q) := by gcongr
      _ = (m.choose q:ℝ)*t^q*((m.choose q:ℝ)*t^q) := by rw [two_mul, pow_add]; ring
      _ ≤ _ := by simpa [two_mul,pow_add] using hb

theorem large_term_count_bound (m k : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : 0 < 1-p)
    (hp2 : 1/2 ≤ p) (hp3 : p^2 ≤ 1-p) (hkm : k ≤ m) (hk : p*m ≤ (k:ℝ)+1) :
    (∑ q ∈ Finset.range (m+1), (m.choose q:ℝ)*((m-(k-q)).choose q:ℝ)) ≤
      ((m:ℝ)+1)*(p/(1-p))^2*exp (2*m*binEntropy p) := by
  let t := p/(1-p)
  have ht0 : 0 < t := div_pos hp hp1
  have ht : 1≤t := (le_div_iff₀ hp1).mpr (by linarith)
  have hb : t+1=(1-p)⁻¹ := by dsimp [t]; field_simp; ring
  have hs : t^2≤t+1 := by
    rw [hb]; dsimp [t]; rw [div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos hp1)).mpr
    simpa [pow_two,←mul_assoc, hp1.ne'] using hp3
  have he : exp (2*m*binEntropy p)*t^(2*p*m)=(t+1)^(2*m) := by
    apply Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity))
    rw [Real.log_mul (by positivity) (by positivity),Real.log_rpow ht0,Real.log_exp,
      Real.log_pow,hb,Real.log_inv]
    dsimp [t]
    rw [Real.log_div hp.ne' hp1.ne']
    simp [Real.binEntropy, Real.log_inv]; ring
  have one (q : ℕ) :
      (m.choose q:ℝ)*((m-(k-q)).choose q:ℝ) ≤ t^2*exp (2*m*binEntropy p) := by
    have hh := tilted_pairs m k q hkm t ht hs
    have ht2 := Real.rpow_le_rpow_of_exponent_le ht (show 2*p*m ≤ (2:ℝ)*(k+1) by linarith)
    have ht3 : t^((2:ℝ)*((k:ℝ)+1))=t^(2*k)*t^2 := by
      rw [mul_add, mul_one, ←Nat.cast_ofNat (R:=ℝ) (n:=2), ←Nat.cast_mul,
        Real.rpow_add ht0, Real.rpow_natCast,Real.rpow_natCast]
    rw [ht3] at ht2
    apply le_of_mul_le_mul_right (a:=t^(2*p*m)) _ (Real.rpow_pos_of_pos ht0 _)
    calc
      _ ≤ ((m.choose q:ℝ)*((m-(k-q)).choose q:ℝ)*t^(2*k))*t^2 := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left ht2 (by positivity : (0:ℝ)≤(m.choose q:ℝ)*((m-(k-q)).choose q:ℝ))
      _ ≤ (t+1)^(2*m)*t^2 := by gcongr
      _ = _ := by rw [←he]; ring
  calc
    _ ≤ ∑ _q ∈ Finset.range (m+1), t^2*exp (2*m*binEntropy p) := Finset.sum_le_sum (fun q _ => one q)
    _ = _ := by simp [t]; ring
open BipHamCount.Deterministic
theorem solution :
    (∀ (m k q s₁ s₂ s₃ s₄ : ℕ),
      ((chooseSets ((suffix (m:=m) (k-q)).run s₁).1 q).run s₂).1.length *
      ((chooseSets ((suffix (m:=m) 0).run s₃).1 q).run s₄).1.length =
        (m-(k-q)).choose q * m.choose q) ∧
    (∀ m : ℕ,
      (∑ q ∈ Finset.range (m+1), (m.choose q:ℝ)*((m-(kOf m-q)).choose q:ℝ)) ≤
      ((m:ℝ)+1)*(alpha/(1-alpha))^2*Real.exp (2*m*Real.binEntropy alpha)) := by
  refine ⟨large_layer_count,fun m => ?_⟩
  apply large_term_count_bound m (kOf m) alpha <;> try norm_num [alpha]
  · unfold kOf; omega
  · have h := Nat.mod_add_div (60909*m) 100000
    have hr := Nat.mod_lt (60909*m) (by decide : 0 < 100000)
    have hh : 60909*m ≤ (60909*m/100000+1)*100000 := by omega
    have hh' : (60909:ℝ)*m ≤ ((60909*m/100000 : ℕ)+1 : ℝ)*100000 := by exact_mod_cast hh
    unfold kOf
    linarith
