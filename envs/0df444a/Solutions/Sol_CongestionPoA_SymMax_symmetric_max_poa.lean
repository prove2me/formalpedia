-- Prove2me | solution 1 for CongestionPoA.SymMax.symmetric_max_poa
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T04:39:11.809099+00:00
-- url     : https://prove2.me/submissions/5d564796-3b78-4408-b744-a3ff0daa32bf

import Mathlib
import Definitions.Def_CongestionPoA_SymMax_Model



namespace CongestionPoA.SymMax

open Finset

theorem sm_load_eq {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (A : ι → Finset E) (e : E) :
    (load A e : ℝ) = ∑ j, if e ∈ A j then (1:ℝ) else 0 := by
  unfold load
  rw [Finset.card_filter]; push_cast; rfl

theorem sm_load_update {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (A : ι → Finset E) (i : ι) (S : Finset E) (e : E) (he : e ∈ S) :
    (load (Function.update A i S) e : ℝ) = load A e + if e ∈ A i then 0 else 1 := by
  rw [sm_load_eq, sm_load_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have : ∑ j ∈ univ.erase i, (if e ∈ Function.update A i S j then (1:ℝ) else 0)
      = ∑ j ∈ univ.erase i, (if e ∈ A j then (1:ℝ) else 0) :=
    Finset.sum_congr rfl (fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)])
  rw [this, Function.update_self]
  by_cases h : e ∈ A i <;> simp [h, he] <;> ring

theorem sm_dev_cost' {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (G : CongestionGame ι E) (a b : E → ℝ) (hlin : ∀ e k, G.latency e k = a e * k + b e)
    (A : ι → Finset E) (i : ι) (S : Finset E) :
    cost G (Function.update A i S) i
      = ∑ e ∈ S, (a e * ((load A e : ℝ) + if e ∈ A i then 0 else 1) + b e) := by
  unfold cost
  rw [Function.update_self]
  refine Finset.sum_congr rfl (fun e he => ?_)
  rw [hlin, sm_load_update A i S e he]

theorem sm_sumcost {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (A : ι → Finset E) (f : E → ℝ) :
    ∑ i, ∑ e ∈ A i, f e = ∑ e, (load A e : ℝ) * f e := by
  have : ∀ i, ∑ e ∈ A i, f e = ∑ e, if e ∈ A i then f e else 0 := fun i => by
    rw [← Finset.sum_filter]; congr 1; ext; simp
  simp_rw [this]
  rw [Finset.sum_comm]
  congr 1; ext e
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  rfl

/-- deviation of `i` to `P j` costs at most `Σ_{e∈P j} a(n_A+1)+b`. -/
theorem sm_dev_le {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (G : CongestionGame ι E) (a b : E → ℝ) (ha : ∀ e, 0 ≤ a e)
    (hlin : ∀ e k, G.latency e k = a e * k + b e) (hsym : IsSymmetric G)
    (A P : ι → Finset E) (hA : IsPureNash G A) (hP : IsProfile G P) (i j : ι) :
    cost G A i ≤ ∑ e ∈ P j, (a e * ((load A e : ℝ) + 1) + b e) := by
  have hmem : P j ∈ G.strategies i := by rw [hsym i j]; exact hP j
  have h := hA.2 i (P j) hmem
  rw [sm_dev_cost' G a b hlin] at h
  refine h.trans (Finset.sum_le_sum fun e _ => ?_)
  have := ha e
  split_ifs <;> nlinarith

theorem sm_player {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (G : CongestionGame ι E) (a b : E → ℝ) (ha : ∀ e, 0 ≤ a e)
    (hlin : ∀ e k, G.latency e k = a e * k + b e) (hsym : IsSymmetric G)
    (A P : ι → Finset E) (hA : IsPureNash G A) (hP : IsProfile G P) (i : ι) :
    (Fintype.card ι : ℝ) * cost G A i ≤
      ∑ e, a e * ((load P e : ℝ) * (load A e : ℝ) + (load P e : ℝ)) + ∑ e, b e * (load P e : ℝ) := by
  have h1 : (Fintype.card ι : ℝ) * cost G A i = ∑ _j : ι, cost G A i := by
    simp [Finset.card_univ]
  have h2 := Finset.sum_le_sum (fun j (_ : j ∈ (univ : Finset ι)) =>
    sm_dev_le G a b ha hlin hsym A P hA hP i j)
  rw [sm_sumcost] at h2
  rw [h1]
  refine h2.trans (le_of_eq ?_)
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun e _ => by ring)

theorem sm_int (x y : ℕ) : 3 * ((y : ℝ) * x + y) ≤ (x : ℝ) ^ 2 + 5 * (y : ℝ) ^ 2 := by
  have key : 3 * (y * x + y) ≤ x ^ 2 + 5 * y ^ 2 := by
    rcases Nat.lt_or_ge y 2 with hy | hy
    · interval_cases y
      · simp
      · rcases Nat.lt_or_ge x 2 with hx | hx
        · interval_cases x <;> simp
        · nlinarith
    · nlinarith [sq_nonneg ((2 * x : ℤ) - 3 * y)]
  exact_mod_cast key

theorem sm_ub_core (ι E : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype E]
    [DecidableEq E] (G : CongestionGame ι E) (A P : ι → Finset E)
    (hlin : IsLinear G) (hsym : IsSymmetric G) (hA : IsPureNash G A) (hP : IsProfile G P) :
    maxCost G A ≤ 5 / 2 * maxCost G P := by
  obtain ⟨a, b, ha, hb, hl⟩ := hlin
  have hsc : ∀ X : ι → Finset E, sumCost G X
      = ∑ e, a e * (load X e : ℝ) ^ 2 + ∑ e, b e * (load X e : ℝ) := by
    intro X
    unfold sumCost cost
    simp_rw [hl]
    rw [sm_sumcost, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun e _ => by ring)
  set N := (Fintype.card ι : ℝ) with hNdef
  have hNpos : (0:ℝ) < N := by
    rw [hNdef]; exact_mod_cast Fintype.card_pos
  set R := ∑ e, a e * ((load P e : ℝ) * (load A e : ℝ) + (load P e : ℝ)) + ∑ e, b e * (load P e : ℝ)
  have hpl : ∀ i, N * cost G A i ≤ R := fun i => sm_player G a b ha hl hsym A P hA hP i
  set Q := ∑ e, a e * ((load P e : ℝ) * (load A e : ℝ) + (load P e : ℝ))
  set SAa := ∑ e, a e * (load A e : ℝ) ^ 2
  set SAb := ∑ e, b e * (load A e : ℝ)
  set SPa := ∑ e, a e * (load P e : ℝ) ^ 2
  set SPb := ∑ e, b e * (load P e : ℝ)
  have hQ : 3 * Q ≤ SAa + 5 * SPa := by
    simp only [Q, SAa, SPa, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun e _ => by
      have := sm_int (load A e) (load P e)
      have := ha e
      nlinarith)
  have hSAb : 0 ≤ SAb := Finset.sum_nonneg (fun e _ => mul_nonneg (hb e) (Nat.cast_nonneg _))
  have hSPb : 0 ≤ SPb := Finset.sum_nonneg (fun e _ => mul_nonneg (hb e) (Nat.cast_nonneg _))
  -- SUM(A) ≤ R
  have hsumA : N * sumCost G A ≤ N * R := by
    unfold sumCost
    rw [Finset.mul_sum]
    calc ∑ i, N * cost G A i ≤ ∑ _i : ι, R := Finset.sum_le_sum fun i _ => hpl i
      _ = N * R := by simp [Finset.card_univ, hNdef]
  have hsumA' : sumCost G A ≤ R := le_of_mul_le_mul_left hsumA hNpos
  rw [hsc A] at hsumA'
  have hSA : SAa + SAb ≤ 5 / 2 * (SPa + SPb) := by
    have : R = Q + SPb := rfl
    nlinarith
  -- SUM(P) ≤ N * MAX(P)
  have hmaxP : SPa + SPb ≤ N * maxCost G P := by
    rw [← hsc P]
    unfold sumCost
    calc ∑ i, cost G P i ≤ ∑ _i : ι, maxCost G P :=
          Finset.sum_le_sum fun i _ => Finset.le_sup' (cost G P) (Finset.mem_univ i)
      _ = N * maxCost G P := by simp [Finset.card_univ, hNdef]
  unfold maxCost
  apply Finset.sup'_le
  intro i _
  have h1 := hpl i
  have hR : R ≤ 5 / 2 * (SPa + SPb) := by
    have : R = Q + SPb := rfl
    nlinarith
  have h2 : N * cost G A i ≤ N * (5 / 2 * maxCost G P) := by
    have : maxCost G P = Finset.univ.sup' Finset.univ_nonempty (cost G P) := rfl
    nlinarith
  have := le_of_mul_le_mul_left h2 hNpos
  simpa [maxCost] using this

abbrev T8Fac (n : ℕ) := (Fin (n+1) × Fin n × Fin n) ⊕ Unit

def t8isP {n : ℕ} (i : Fin (n+1)) : T8Fac n → Bool
  | .inl x => decide (x.1 = i)
  | .inr _ => false

def t8isA {n : ℕ} (m : Fin n) : T8Fac n → Bool
  | .inl x => decide (x.2.1 = m) || decide (x.2.2 = m)
  | .inr _ => false

def t8P {n : ℕ} (i : Fin (n+1)) : Finset (T8Fac n) := univ.filter (fun e => t8isP i e = true)
def t8A' {n : ℕ} (m : Fin n) : Finset (T8Fac n) := univ.filter (fun e => t8isA m e = true)
def t8Z (n : ℕ) : Finset (T8Fac n) := {Sum.inr ()}

def t8A {n : ℕ} : Fin (n+1) → Finset (T8Fac n) := Fin.cases (t8Z n) (fun m => t8A' m)

noncomputable def t8a1 (n : ℕ) : ℝ := ((n:ℝ) - 1) * ((n:ℝ) + 6)
noncomputable def t8a2 (n : ℕ) : ℝ := (n:ℝ) - 2
noncomputable def t8bz (n : ℕ) : ℝ := 2 * n * t8a1 n + 3 * n * ((n:ℝ) - 1) * t8a2 n
noncomputable def t8W (n : ℕ) : ℝ := n * t8a1 n + n * ((n:ℝ) - 1) * t8a2 n

noncomputable def t8wt {n : ℕ} (j k : Fin n) : ℝ := if j = k then t8a1 n else t8a2 n

noncomputable def t8a {n : ℕ} : T8Fac n → ℝ
  | .inl x => t8wt x.2.1 x.2.2
  | .inr _ => 0
noncomputable def t8b {n : ℕ} : T8Fac n → ℝ
  | .inl _ => 0
  | .inr _ => t8bz n

noncomputable def t8G (n : ℕ) : CongestionGame (Fin (n+1)) (T8Fac n) where
  strategies := fun _ => (univ.image t8P) ∪ (univ.image t8A') ∪ {t8Z n}
  latency := fun e k => t8a e * k + t8b e

-- sum over the facilities as a triple sum
theorem t8_sum (n : ℕ) (f : T8Fac n → ℝ) :
    ∑ e, f e = ∑ i : Fin (n+1), ∑ j : Fin n, ∑ k : Fin n, f (.inl (i, j, k)) + f (.inr ()) := by
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp [Fintype.sum_prod_type]

-- generic indicator sum
theorem t8_ind (n : ℕ) (m : Fin n) (c0 c1 c2 c3 c4 : ℝ) :
    ∑ j : Fin n, ∑ k : Fin n, (c0 + (if j = m then c1 else 0) + (if k = m then c2 else 0)
      + (if j = k then c3 else 0) + (if j = k ∧ j = m then c4 else 0))
      = c0 * n ^ 2 + c1 * n + c2 * n + c3 * n + c4 := by
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have h1 : ∑ j : Fin n, ∑ k : Fin n, (if j = k ∧ j = m then c4 else 0) = c4 := by
    have : ∀ j : Fin n, ∑ k : Fin n, (if j = k ∧ j = m then c4 else 0)
        = if j = m then c4 else 0 := by
      intro j
      by_cases hj : j = m
      · subst hj; simp
      · simp [hj]
    simp [this]
  rw [h1]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq']
  ring

theorem t8_ind0 (n : ℕ) (c0 c3 : ℝ) :
    ∑ j : Fin n, ∑ k : Fin n, (c0 + (if j = k then c3 else 0)) = c0 * n ^ 2 + c3 * n := by
  simp [Finset.sum_add_distrib, Finset.sum_ite_eq]
  ring

theorem t8_memA' {n : ℕ} (m : Fin n) (i : Fin (n+1)) (j k : Fin n) :
    (Sum.inl (i, j, k) : T8Fac n) ∈ t8A' m ↔ (j = m ∨ k = m) := by
  rw [t8A', Finset.mem_filter]; simp [t8isA]

theorem t8_memA'_inr {n : ℕ} (m : Fin n) : (Sum.inr () : T8Fac n) ∉ t8A' m := by
  rw [t8A', Finset.mem_filter]; simp [t8isA]

theorem t8_memP {n : ℕ} (p : Fin (n+1)) (i : Fin (n+1)) (j k : Fin n) :
    (Sum.inl (i, j, k) : T8Fac n) ∈ t8P p ↔ i = p := by
  rw [t8P, Finset.mem_filter]; simp [t8isP]

theorem t8_memP_inr {n : ℕ} (p : Fin (n+1)) : (Sum.inr () : T8Fac n) ∉ t8P p := by
  rw [t8P, Finset.mem_filter]; simp [t8isP]

theorem t8_loadA {n : ℕ} (i : Fin (n+1)) (j k : Fin n) :
    (load t8A (Sum.inl (i, j, k) : T8Fac n) : ℝ) = if j = k then 1 else 2 := by
  unfold load
  rw [Finset.card_filter]
  push_cast
  rw [Fin.sum_univ_succ]
  simp only [t8A, Fin.cases_zero, Fin.cases_succ, t8Z, Finset.mem_singleton, t8_memA']
  simp only [reduceCtorEq, if_false, zero_add]
  by_cases h : j = k
  · subst h; simp [Finset.sum_ite_eq]
  · have : ∀ x : Fin n, (if j = x ∨ k = x then (1:ℝ) else 0)
        = (if j = x then 1 else 0) + (if k = x then 1 else 0) := by
      intro x
      by_cases h1 : j = x <;> by_cases h2 : k = x <;> simp_all
    simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, h]
    norm_num

theorem t8_memA {n : ℕ} (p : Fin (n+1)) (i : Fin (n+1)) (j k : Fin n) :
    (Sum.inl (i, j, k) : T8Fac n) ∈ t8A p ↔ ∃ m : Fin n, p = m.succ ∧ (j = m ∨ k = m) := by
  refine Fin.cases ?_ (fun m => ?_) p
  · simp only [t8A, Fin.cases_zero, t8Z, Finset.mem_singleton, reduceCtorEq, false_iff]
    rintro ⟨x, hx, _⟩; exact absurd hx.symm (Fin.succ_ne_zero x)
  · simp only [t8A, Fin.cases_succ, t8_memA']
    constructor
    · intro h; exact ⟨m, rfl, h⟩
    · rintro ⟨m', hm, h⟩
      rw [Fin.succ_inj] at hm
      subst hm; exact h

theorem t8_loadP {n : ℕ} (i : Fin (n+1)) (j k : Fin n) :
    load (fun p : Fin (n+1) => t8P (n := n) p) (Sum.inl (i, j, k) : T8Fac n) = 1 := by
  unfold load
  rw [Finset.card_eq_one]
  refine ⟨i, ?_⟩
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, t8_memP, Finset.mem_singleton]
  exact eq_comm

theorem t8_lat (n : ℕ) (e : T8Fac n) (c : ℕ) :
    (t8G n).latency e c = t8a e * c + t8b e := rfl

theorem t8_a_nonneg {n : ℕ} (hn : 2 ≤ n) (e : T8Fac n) : 0 ≤ t8a e := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  cases e with
  | inl x => simp only [t8a, t8wt, t8a1, t8a2]; split_ifs <;> nlinarith
  | inr _ => simp [t8a]

theorem t8_b_nonneg {n : ℕ} (hn : 2 ≤ n) (e : T8Fac n) : 0 ≤ t8b e := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  cases e with
  | inl x => simp [t8b]
  | inr _ =>
    simp only [t8b, t8bz, t8a1, t8a2]
    have h1 : 0 ≤ (n:ℝ) - 1 := by linarith
    have h2 : 0 ≤ (n:ℝ) - 2 := by linarith
    positivity

-- cost of a strategy-sum in terms of the triple sum
theorem t8_sum_P {n : ℕ} (i : Fin (n+1)) (f : T8Fac n → ℝ) :
    ∑ e ∈ t8P i, f e = ∑ j : Fin n, ∑ k : Fin n, f (.inl (i, j, k)) := by
  rw [t8P, Finset.sum_filter, t8_sum]
  simp [t8isP]

theorem t8_sum_A {n : ℕ} (m : Fin n) (f : T8Fac n → ℝ) :
    ∑ e ∈ t8A' m, f e = ∑ i : Fin (n+1), ∑ j : Fin n, ∑ k : Fin n,
      (if j = m ∨ k = m then f (.inl (i, j, k)) else 0) := by
  rw [t8A', Finset.sum_filter, t8_sum]
  simp [t8isA]


theorem t8_const (n : ℕ) (c : ℝ) : ∑ _i : Fin (n+1), c = ((n:ℝ) + 1) * c := by
  simp

theorem t8_cost_succ {n : ℕ} (m : Fin n) :
    cost (t8G n) t8A m.succ = ((n:ℝ) + 1) * (t8a1 n + 4 * ((n:ℝ) - 1) * t8a2 n) := by
  unfold cost
  rw [show t8A m.succ = t8A' m from rfl, t8_sum_A]
  have hpt : ∀ (i : Fin (n+1)) (j k : Fin n),
      (if j = m ∨ k = m then (t8G n).latency (.inl (i, j, k)) (load t8A (.inl (i, j, k) : T8Fac n))
        else 0) = (0 + (if j = m then 2 * t8a2 n else 0) + (if k = m then 2 * t8a2 n else 0)
          + (if j = k then 0 else 0) + (if j = k ∧ j = m then t8a1 n - 4 * t8a2 n else 0)) := by
    intro i j k
    rw [t8_lat]
    rw [t8_loadA]
    simp only [t8a, t8b, t8wt]
    by_cases h1 : j = m <;> by_cases h2 : k = m <;> by_cases h3 : j = k <;> simp_all <;> ring
  simp_rw [hpt]
  simp_rw [t8_ind]
  rw [t8_const]
  ring

theorem t8_cost_zero (n : ℕ) : cost (t8G n) t8A 0 = t8bz n := by
  unfold cost
  simp [t8A, t8Z, t8_lat, t8a, t8b]

theorem t8_dev {n : ℕ} (p : Fin (n+1)) (S : Finset (T8Fac n)) :
    cost (t8G n) (Function.update t8A p S) p
      = ∑ e ∈ S, (t8a e * ((load t8A e : ℝ) + if e ∈ t8A p then 0 else 1) + t8b e) :=
  sm_dev_cost' (t8G n) t8a t8b (fun e k => t8_lat n e k) t8A p S

theorem t8_dev_Z {n : ℕ} (p : Fin (n+1)) :
    cost (t8G n) (Function.update t8A p (t8Z n)) p = t8bz n := by
  rw [t8_dev]
  simp [t8Z, t8a, t8b]

theorem t8_dev0_P {n : ℕ} (i : Fin (n+1)) :
    cost (t8G n) (Function.update t8A 0 (t8P i)) 0
      = 3 * t8a2 n * (n:ℝ) ^ 2 + (2 * t8a1 n - 3 * t8a2 n) * n := by
  rw [t8_dev, t8_sum_P]
  have hpt : ∀ (j k : Fin n),
      (t8a (.inl (i, j, k) : T8Fac n) * ((load t8A (.inl (i, j, k) : T8Fac n) : ℝ)
        + if (.inl (i, j, k) : T8Fac n) ∈ t8A 0 then 0 else 1) + t8b (.inl (i, j, k) : T8Fac n))
      = 3 * t8a2 n + (if j = k then 2 * t8a1 n - 3 * t8a2 n else 0) := by
    intro j k
    rw [t8_loadA]
    have : (.inl (i, j, k) : T8Fac n) ∉ t8A 0 := by simp [t8A, t8Z]
    simp only [this, if_false, t8a, t8b, t8wt]
    by_cases h3 : j = k <;> simp [h3] <;> ring
  simp_rw [hpt]
  rw [t8_ind0]

theorem t8_dev0_A {n : ℕ} (m : Fin n) :
    cost (t8G n) (Function.update t8A 0 (t8A' m)) 0
      = ((n:ℝ) + 1) * (6 * t8a2 n * n + 2 * t8a1 n - 6 * t8a2 n) := by
  rw [t8_dev, t8_sum_A]
  have hpt : ∀ (i : Fin (n+1)) (j k : Fin n),
      (if j = m ∨ k = m then (t8a (.inl (i, j, k) : T8Fac n) * ((load t8A (.inl (i, j, k) : T8Fac n) : ℝ)
        + if (.inl (i, j, k) : T8Fac n) ∈ t8A 0 then 0 else 1) + t8b (.inl (i, j, k) : T8Fac n)) else 0)
      = (0 + (if j = m then 3 * t8a2 n else 0) + (if k = m then 3 * t8a2 n else 0)
          + (if j = k then 0 else 0) + (if j = k ∧ j = m then 2 * t8a1 n - 6 * t8a2 n else 0)) := by
    intro i j k
    rw [t8_loadA]
    have : (.inl (i, j, k) : T8Fac n) ∉ t8A 0 := by simp [t8A, t8Z]
    simp only [this, if_false, t8a, t8b, t8wt]
    by_cases h1 : j = m <;> by_cases h2 : k = m <;> by_cases h3 : j = k <;> simp_all <;> ring
  simp_rw [hpt]
  simp_rw [t8_ind]
  rw [t8_const]
  ring

theorem t8_devS_P {n : ℕ} (m : Fin n) (i : Fin (n+1)) :
    cost (t8G n) (Function.update t8A m.succ (t8P i)) m.succ
      = 3 * t8a2 n * (n:ℝ) ^ 2 - 2 * t8a2 n * n + (2 * t8a1 n - 3 * t8a2 n) * n
        + (2 * t8a2 n - t8a1 n) := by
  rw [t8_dev, t8_sum_P]
  have hpt : ∀ (j k : Fin n),
      (t8a (.inl (i, j, k) : T8Fac n) * ((load t8A (.inl (i, j, k) : T8Fac n) : ℝ)
        + if (.inl (i, j, k) : T8Fac n) ∈ t8A m.succ then 0 else 1) + t8b (.inl (i, j, k) : T8Fac n))
      = (3 * t8a2 n + (if j = m then -t8a2 n else 0) + (if k = m then -t8a2 n else 0)
          + (if j = k then 2 * t8a1 n - 3 * t8a2 n else 0)
          + (if j = k ∧ j = m then 2 * t8a2 n - t8a1 n else 0)) := by
    intro j k
    rw [t8_loadA]
    have hm : (.inl (i, j, k) : T8Fac n) ∈ t8A m.succ ↔ (j = m ∨ k = m) := by
      simp only [t8A, Fin.cases_succ, t8_memA']
    simp only [hm, t8a, t8b, t8wt]
    by_cases h1 : j = m <;> by_cases h2 : k = m <;> by_cases h3 : j = k <;> simp_all <;> ring
  simp_rw [hpt]
  rw [t8_ind]
  ring

theorem t8_devS_A {n : ℕ} (hn : 2 ≤ n) (m m' : Fin n) :
    cost (t8G n) t8A m'.succ ≤ cost (t8G n) (Function.update t8A m.succ (t8A' m')) m.succ := by
  rw [t8_dev]
  unfold cost
  rw [show t8A m'.succ = t8A' m' from rfl, show t8A m.succ = t8A' m from rfl]
  apply Finset.sum_le_sum
  intro e _
  rw [t8_lat]
  have := t8_a_nonneg hn e
  by_cases h : e ∈ t8A' m <;> simp only [h, if_true, if_false] <;> nlinarith

theorem t8_costP {n : ℕ} (i : Fin (n+1)) :
    cost (t8G n) (fun p => t8P p) i = t8W n := by
  unfold cost
  rw [t8_sum_P]
  have hpt : ∀ (j k : Fin n),
      (t8G n).latency (.inl (i, j, k)) (load (fun p : Fin (n+1) => t8P (n := n) p) (.inl (i, j, k)))
      = t8a2 n + (if j = k then t8a1 n - t8a2 n else 0) := by
    intro j k
    rw [t8_lat, t8_loadP]
    simp only [t8a, t8b, t8wt]
    by_cases h3 : j = k <;> simp [h3]
  simp_rw [hpt]
  rw [t8_ind0, t8W]
  ring

theorem t8_lower {n : ℕ} (hn : 2 ≤ n) (Q : Fin (n+1) → Finset (T8Fac n)) (p : Fin (n+1)) :
    ∑ e ∈ Q p, (t8a e + t8b e) ≤ cost (t8G n) Q p := by
  unfold cost
  apply Finset.sum_le_sum
  intro e he
  rw [t8_lat]
  have h1 : (1:ℝ) ≤ load Q e := by
    have : 0 < load Q e := by
      unfold load
      exact Finset.card_pos.mpr ⟨p, by simp [he]⟩
    exact_mod_cast this
  have := t8_a_nonneg hn e
  nlinarith

theorem t8_low_P {n : ℕ} (i : Fin (n+1)) :
    ∑ e ∈ t8P i, (t8a e + t8b e) = t8W n := by
  rw [t8_sum_P]
  have hpt : ∀ (j k : Fin n), (t8a (.inl (i, j, k) : T8Fac n) + t8b (.inl (i, j, k) : T8Fac n))
      = t8a2 n + (if j = k then t8a1 n - t8a2 n else 0) := by
    intro j k
    simp only [t8a, t8b, t8wt]
    by_cases h3 : j = k <;> simp [h3]
  simp_rw [hpt]
  rw [t8_ind0, t8W]
  ring

theorem t8_low_A {n : ℕ} (m : Fin n) :
    ∑ e ∈ t8A' m, (t8a e + t8b e) = ((n:ℝ) + 1) * (2 * t8a2 n * n + t8a1 n - 2 * t8a2 n) := by
  rw [t8_sum_A]
  have hpt : ∀ (i : Fin (n+1)) (j k : Fin n),
      (if j = m ∨ k = m then (t8a (.inl (i, j, k) : T8Fac n) + t8b (.inl (i, j, k) : T8Fac n)) else 0)
      = (0 + (if j = m then t8a2 n else 0) + (if k = m then t8a2 n else 0)
          + (if j = k then 0 else 0) + (if j = k ∧ j = m then t8a1 n - 2 * t8a2 n else 0)) := by
    intro i j k
    simp only [t8a, t8b, t8wt]
    by_cases h1 : j = m <;> by_cases h2 : k = m <;> by_cases h3 : j = k <;> simp_all <;> ring
  simp_rw [hpt]
  simp_rw [t8_ind]
  rw [t8_const]
  ring

theorem t8_low_Z (n : ℕ) : ∑ e ∈ t8Z n, (t8a e + t8b e) = t8bz n := by
  simp [t8Z, t8a, t8b]

theorem t8_mem_strat {n : ℕ} (p : Fin (n+1)) (S : Finset (T8Fac n)) :
    S ∈ (t8G n).strategies p ↔ (∃ i, S = t8P i) ∨ (∃ m, S = t8A' m) ∨ S = t8Z n := by
  simp only [t8G, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · rintro ((⟨i, rfl⟩ | ⟨m, rfl⟩) | rfl)
    · exact Or.inl ⟨i, rfl⟩
    · exact Or.inr (Or.inl ⟨m, rfl⟩)
    · exact Or.inr (Or.inr rfl)
  · rintro (⟨i, rfl⟩ | ⟨m, rfl⟩ | rfl)
    · exact Or.inl (Or.inl ⟨i, rfl⟩)
    · exact Or.inl (Or.inr ⟨m, rfl⟩)
    · exact Or.inr rfl

theorem t8_core (N : ℕ) [NeZero N] (hN : 3 ≤ N) :
    ∃ (E : Type) (_ : Fintype E) (_ : DecidableEq E) (G : CongestionGame (Fin N) E)
      (A P : Fin N → Finset E),
      IsLinear G ∧ IsSymmetric G ∧ IsPureNash G A ∧ IsProfile G P ∧
      (∀ Q : Fin N → Finset E, IsProfile G Q → maxCost G P ≤ maxCost G Q) ∧
      0 < maxCost G P ∧
      maxCost G A = (5 * N + 1) / (2 * N + 2) * maxCost G P := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 2 ≤ n := by omega
  have hnr : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hy : (0:ℝ) ≤ (n:ℝ) - 2 := by linarith
  have hy2 := mul_nonneg hy hy
  have hy3 := mul_nonneg hy2 hy
  have hW : 0 < t8W n := by
    simp only [t8W, t8a1, t8a2]; nlinarith [hy, hy2, hy3, mul_nonneg hy (by linarith : (0:ℝ) ≤ n), mul_nonneg hy2 (by linarith : (0:ℝ) ≤ n)]
  have hbzW : t8W n ≤ t8bz n := by
    simp only [t8W, t8bz, t8a1, t8a2]; nlinarith [hy, hy2, hy3, mul_nonneg hy (by linarith : (0:ℝ) ≤ n), mul_nonneg hy2 (by linarith : (0:ℝ) ≤ n)]
  have hcostA : ∀ p, cost (t8G n) t8A p ≤ t8bz n := by
    intro p
    refine Fin.cases ?_ (fun m => ?_) p
    · rw [t8_cost_zero]
    · rw [t8_cost_succ]; simp only [t8bz, t8a1, t8a2]; nlinarith [hy, hy2, hy3, mul_nonneg hy (by linarith : (0:ℝ) ≤ n), mul_nonneg hy2 (by linarith : (0:ℝ) ≤ n)]
  have hmaxA : maxCost (t8G n) t8A = t8bz n := by
    unfold maxCost
    apply le_antisymm
    · exact Finset.sup'_le _ _ (fun p _ => hcostA p)
    · rw [← t8_cost_zero n]; exact Finset.le_sup' _ (Finset.mem_univ _)
  have hmaxP : maxCost (t8G n) (fun p => t8P p) = t8W n := by
    unfold maxCost
    apply le_antisymm
    · exact Finset.sup'_le _ _ (fun p _ => (t8_costP p).le)
    · rw [← t8_costP (n := n) 0]; exact Finset.le_sup' _ (Finset.mem_univ _)
  refine ⟨T8Fac n, inferInstance, inferInstance, t8G n, t8A, fun p => t8P p, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨t8a, t8b, t8_a_nonneg hn, t8_b_nonneg hn, fun e k => t8_lat n e k⟩
  · intro i j; rfl
  · have hprof : IsProfile (t8G n) t8A := by
      intro p
      rw [t8_mem_strat]
      refine Fin.cases ?_ (fun m => ?_) p
      · exact Or.inr (Or.inr rfl)
      · exact Or.inr (Or.inl ⟨m, rfl⟩)
    refine ⟨hprof, ?_⟩
    intro p S hS
    rw [t8_mem_strat] at hS
    rcases hS with ⟨i, rfl⟩ | ⟨m', rfl⟩ | rfl
    · refine Fin.cases ?_ (fun m => ?_) p
      · rw [t8_cost_zero, t8_dev0_P]; simp only [t8bz]; nlinarith [hy, hy2, hy3, mul_nonneg hy (by linarith : (0:ℝ) ≤ n), mul_nonneg hy2 (by linarith : (0:ℝ) ≤ n)]
      · rw [t8_cost_succ, t8_devS_P]; simp only [t8a1, t8a2]; nlinarith [hy, hy2, hy3, mul_nonneg hy (by linarith : (0:ℝ) ≤ n), mul_nonneg hy2 (by linarith : (0:ℝ) ≤ n)]
    · refine Fin.cases ?_ (fun m => ?_) p
      · rw [t8_cost_zero, t8_dev0_A]; simp only [t8bz, t8a1, t8a2]; nlinarith [hy, hy2, hy3, mul_nonneg hy (by linarith : (0:ℝ) ≤ n), mul_nonneg hy2 (by linarith : (0:ℝ) ≤ n)]
      · refine le_trans (le_of_eq ?_) (t8_devS_A hn m m')
        rw [t8_cost_succ, t8_cost_succ]
    · rw [t8_dev_Z]; exact hcostA p
  · intro p
    rw [t8_mem_strat]; exact Or.inl ⟨p, rfl⟩
  · intro Q hQ
    rw [hmaxP]
    have h0 := t8_lower hn Q 0
    have h1 : t8W n ≤ ∑ e ∈ Q 0, (t8a e + t8b e) := by
      have := hQ 0
      rw [t8_mem_strat] at this
      rcases this with ⟨i, hi⟩ | ⟨m, hm⟩ | hz
      · rw [hi, t8_low_P]
      · rw [hm, t8_low_A]; simp only [t8W, t8a1, t8a2]; nlinarith [hy, hy2, hy3, mul_nonneg hy (by linarith : (0:ℝ) ≤ n), mul_nonneg hy2 (by linarith : (0:ℝ) ≤ n)]
      · rw [hz, t8_low_Z]; exact hbzW
    have h2 : cost (t8G n) Q 0 ≤ maxCost (t8G n) Q := Finset.le_sup' _ (Finset.mem_univ _)
    linarith
  · rw [hmaxP]; exact hW
  · rw [hmaxA, hmaxP]
    simp only [t8bz, t8W, t8a1, t8a2]
    push_cast
    field_simp
    ring


theorem smp_core :
    (∀ (ι E : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype E] [DecidableEq E]
        (G : CongestionGame ι E) (A P : ι → Finset E),
        IsLinear G → IsSymmetric G → IsPureNash G A → IsProfile G P →
        maxCost G A ≤ 5 / 2 * maxCost G P) ∧
    (∀ (N : ℕ) [NeZero N], 3 ≤ N →
      ∃ (E : Type) (_ : Fintype E) (_ : DecidableEq E) (G : CongestionGame (Fin N) E)
        (A P : Fin N → Finset E),
        IsLinear G ∧ IsSymmetric G ∧ IsPureNash G A ∧ IsProfile G P ∧
        (∀ Q : Fin N → Finset E, IsProfile G Q → maxCost G P ≤ maxCost G Q) ∧
        0 < maxCost G P ∧
        maxCost G A = (5 * N + 1) / (2 * N + 2) * maxCost G P) := by
  refine ⟨?_, ?_⟩
  · intro ι E _ _ _ _ _ G A P hl hs hA hP
    exact sm_ub_core ι E G A P hl hs hA hP
  · intro N _ hN
    exact t8_core N hN

end CongestionPoA.SymMax

open CongestionPoA.SymMax


theorem solution :
    (∀ (ι E : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype E] [DecidableEq E]
        (G : CongestionGame ι E) (A P : ι → Finset E),
        IsLinear G → IsSymmetric G → IsPureNash G A → IsProfile G P →
        maxCost G A ≤ 5 / 2 * maxCost G P) ∧
    (∀ (N : ℕ) [NeZero N], 3 ≤ N →
      ∃ (E : Type) (_ : Fintype E) (_ : DecidableEq E) (G : CongestionGame (Fin N) E)
        (A P : Fin N → Finset E),
        IsLinear G ∧ IsSymmetric G ∧ IsPureNash G A ∧ IsProfile G P ∧
        (∀ Q : Fin N → Finset E, IsProfile G Q → maxCost G P ≤ maxCost G Q) ∧
        0 < maxCost G P ∧
        maxCost G A = (5 * N + 1) / (2 * N + 2) * maxCost G P) := by
  exact smp_core
