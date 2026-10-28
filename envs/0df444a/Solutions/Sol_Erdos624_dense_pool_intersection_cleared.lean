-- Prove2me | solution 1 for Erdos624.dense_pool_intersection_cleared
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-24T08:47:24.075013+00:00
-- url     : https://prove2.me/submissions/33c9f971-70a8-4e65-bfa3-baa6cd502284

import Mathlib

set_option maxHeartbeats 8000000

/-!
Honesty: does not settle PAIR / Step 17 / #624.
Credit: GPT 6.1 Sol -> Ethan Cheung; Lean by Grok Bot (Oct 24 2026).
-/

namespace E624R9

open Finset BigOperators Nat

/-- `b = 2^{q+1} a^q`. -/
def bOf (a q : ℕ) : ℕ := 2 ^ (q + 1) * a ^ q

lemma bOf_pos {a q : ℕ} (ha : 1 ≤ a) : 0 < bOf a q := by
  unfold bOf
  exact Nat.mul_pos (Nat.two_pow_pos _) (Nat.pow_pos (by omega))

/-- Cleared binomial lower bound. -/
lemma factorial_mul_choose_ge_pow (d q : ℕ) :
    q.factorial * d.choose q ≥ (d + 1 - q) ^ q := by
  have hEq : q.factorial * d.choose q = d.descFactorial q :=
    (Nat.descFactorial_eq_factorial_mul_choose d q).symm
  rw [hEq]
  exact Nat.pow_sub_le_descFactorial d q

lemma factorial_mul_choose_le_pow (g q : ℕ) :
    q.factorial * g.choose q ≤ g ^ q := by
  have h := Nat.descFactorial_le_pow g q
  rwa [Nat.descFactorial_eq_factorial_mul_choose] at h

/-- Power-mean on ℕ. -/
lemma pow_sum_le_card_mul_sum_pow_nat {α : Type*} (s : Finset α) (z : α → ℕ)
    (q : ℕ) (hq : 1 ≤ q) :
    (∑ x ∈ s, z x) ^ q ≤ (#s) ^ (q - 1) * ∑ x ∈ s, (z x) ^ q := by
  obtain ⟨q', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hq)
  simpa using (pow_sum_le_card_mul_sum_pow (s := s) (f := z)
    (fun _ _ => Nat.zero_le _) q')

/-- Number of pools in `G` containing `x`. -/
def degree {U C : Type*} [DecidableEq U] [DecidableEq C]
    (G : Finset C) (V : C → Finset U) (x : U) : ℕ :=
  #{u ∈ G | x ∈ V u}

lemma sum_degree_univ {U C : Type*} [Fintype U] [DecidableEq U] [DecidableEq C]
    (G : Finset C) (V : C → Finset U) :
    ∑ x : U, degree G V x = ∑ u ∈ G, #(V u) := by
  classical
  unfold degree
  calc ∑ x : U, #{u ∈ G | x ∈ V u}
      = ∑ x : U, ∑ u ∈ G, (if x ∈ V u then (1 : ℕ) else 0) := by
          refine Fintype.sum_congr _ _ fun x => ?_
          rw [sum_boole]; rfl
    _ = ∑ u ∈ G, ∑ x : U, (if x ∈ V u then (1 : ℕ) else 0) := by rw [Finset.sum_comm]
    _ = ∑ u ∈ G, #(V u) := by
          refine sum_congr rfl fun u _ => ?_
          simp [sum_boole]

/-- `z = d + 1 - q` (same as `d - (q - 1)` for `q ≥ 1`). -/
def excess (d q : ℕ) : ℕ := d + 1 - q

lemma le_excess_add (d q : ℕ) : d ≤ excess d q + (q - 1) ∨ q = 0 := by
  by_cases hq : q = 0
  · exact Or.inr hq
  · left; unfold excess; omega

lemma sum_excess_lower {U C : Type*} [Fintype U] [DecidableEq U] [DecidableEq C]
    (G : Finset C) (V : C → Finset U) (a q : ℕ)
    (ha : 1 ≤ a) (hq : 1 ≤ q)
    (hPool : ∀ u ∈ G, a * #(V u) ≥ Fintype.card U)
    (hg : 2 * a * (q - 1) ≤ #G) :
    2 * a * ∑ x : U, excess (degree G V x) q ≥ #G * Fintype.card U := by
  set n := Fintype.card U
  set g := #G
  set Z := ∑ x : U, excess (degree G V x) q
  have hsumV : a * ∑ u ∈ G, #(V u) ≥ g * n := by
    calc a * ∑ u ∈ G, #(V u)
        = ∑ u ∈ G, a * #(V u) := by rw [mul_sum]
      _ ≥ ∑ u ∈ G, n := sum_le_sum fun u hu => hPool u hu
      _ = g * n := by simp [sum_const, g]
  have hsumd : ∑ x : U, degree G V x = ∑ u ∈ G, #(V u) := sum_degree_univ G V
  have hexc : ∑ x : U, degree G V x ≤ Z + (q - 1) * n := by
    have hpt : ∀ x : U, degree G V x ≤ excess (degree G V x) q + (q - 1) := by
      intro x
      have := le_excess_add (degree G V x) q
      exact this.resolve_right (by omega)
    calc ∑ x : U, degree G V x
        ≤ ∑ x : U, (excess (degree G V x) q + (q - 1)) :=
          sum_le_sum fun x _ => hpt x
      _ = Z + ∑ x : U, (q - 1) := by rw [sum_add_distrib]
      _ = Z + n * (q - 1) := by simp [sum_const, n]
      _ = Z + (q - 1) * n := by ring
  have h1 : g * n ≤ a * Z + a * (q - 1) * n := by
    have hmul : a * ∑ x : U, degree G V x ≤ a * Z + a * (q - 1) * n := by
      have := Nat.mul_le_mul_left a hexc
      convert this using 1; ring
    rw [hsumd] at hmul
    exact le_trans hsumV hmul
  have hgap : 2 * (a * (q - 1) * n) ≤ g * n := by
    calc 2 * (a * (q - 1) * n) = (2 * a * (q - 1)) * n := by ring
      _ ≤ g * n := Nat.mul_le_mul_right n hg
  have h2 : 2 * (g * n) ≤ 2 * (a * Z) + g * n := by
    have hmul2 := Nat.mul_le_mul_left 2 h1
    have hring : 2 * (a * Z + a * (q - 1) * n) = 2 * (a * Z) + 2 * (a * (q - 1) * n) := by ring
    rw [hring] at hmul2
    exact le_trans hmul2 (Nat.add_le_add_left hgap _)
  have h4 : g * n ≤ 2 * (a * Z) := by omega
  convert h4 using 1; ring


/-- Intersection of pools over `S` (empty → `univ`). -/
def poolInter {U C : Type*} [Fintype U] [DecidableEq U]
    (V : C → Finset U) (S : Finset C) : Finset U :=
  if h : S.Nonempty then S.inf' h V else univ

lemma mem_poolInter {U C : Type*} [Fintype U] [DecidableEq U] [DecidableEq C]
    (V : C → Finset U) (S : Finset C) (x : U) :
    x ∈ poolInter V S ↔ ∀ u ∈ S, x ∈ V u := by
  classical
  unfold poolInter
  split_ifs with h
  · simp [mem_inf']
  · simp [not_nonempty_iff_eq_empty.mp h]

lemma card_poolInter_choose_sum {U C : Type*} [Fintype U] [DecidableEq U] [DecidableEq C]
    (G : Finset C) (V : C → Finset U) (q : ℕ) :
    ∑ S ∈ G.powersetCard q, #(poolInter V S) =
      ∑ x : U, (degree G V x).choose q := by
  classical
  have hL : ∑ S ∈ G.powersetCard q, #(poolInter V S) =
      ∑ S ∈ G.powersetCard q, ∑ x : U, (if x ∈ poolInter V S then (1 : ℕ) else 0) := by
    refine sum_congr rfl fun S _ => ?_
    simp [sum_boole]
  rw [hL, Finset.sum_comm]
  refine Fintype.sum_congr _ _ fun x => ?_
  let Dx : Finset C := {u ∈ G | x ∈ V u}
  have hDxsub : Dx ⊆ G := filter_subset _ _
  have hfilt :
      {S ∈ G.powersetCard q | x ∈ poolInter V S} = Dx.powersetCard q := by
    ext S
    simp only [mem_filter, mem_powersetCard, mem_poolInter]
    constructor
    · intro ⟨⟨hSG, hcard⟩, hx⟩
      exact ⟨fun u hu => mem_filter.mpr ⟨hSG hu, hx u hu⟩, hcard⟩
    · intro ⟨hSDx, hcard⟩
      exact ⟨⟨fun u hu => hDxsub (hSDx hu), hcard⟩,
        fun u hu => (mem_filter.mp (hSDx hu)).2⟩
  have hsum :
      ∑ S ∈ G.powersetCard q, (if x ∈ poolInter V S then (1 : ℕ) else 0) =
        #(Dx.powersetCard q) := by
    rw [← sum_filter, sum_const, smul_eq_mul, mul_one, hfilt]
  rw [hsum, card_powersetCard]
  rfl

/-- Good q-tuples: those with `b · |∩ pools| ≥ n`. -/
def goodTuples {U C : Type*} [Fintype U] [DecidableEq U] [DecidableEq C]
    (G : Finset C) (V : C → Finset U) (a q : ℕ) : Finset (Finset C) :=
  let n := Fintype.card U
  let b := bOf a q
  {S ∈ G.powersetCard q | b * #(poolInter V S) ≥ n}

lemma le_card_univ {U : Type*} [Fintype U] [DecidableEq U] (s : Finset U) :
    #s ≤ Fintype.card U :=
  card_le_card (subset_univ s)

lemma factorial_mul_choose_ge_excess_pow (d q : ℕ) (hq : 1 ≤ q) :
    q.factorial * d.choose q ≥ (excess d q) ^ q := by
  unfold excess
  exact factorial_mul_choose_ge_pow d q

/-- Dense-pool intersection lemma (Sol (6)), multiplication-cleared.
Requires `1 ≤ |U|` (Sol cancels `n > 0`). -/
theorem dense_pool_intersection
    {U C : Type*} [Fintype U] [DecidableEq U] [DecidableEq C]
    (G : Finset C) (V : C → Finset U) (a q : ℕ)
    (ha : 1 ≤ a) (hq : 1 ≤ q) (hn : 1 ≤ Fintype.card U)
    (hPool : ∀ u ∈ G, a * #(V u) ≥ Fintype.card U)
    (hg : 2 * a * (q - 1) ≤ #G) :
    bOf a q * q.factorial * #(goodTuples G V a q) ≥ (#G) ^ q := by
  classical
  set n := Fintype.card U
  set b := bOf a q
  set g := #G
  set Z := ∑ x : U, excess (degree G V x) q
  set good := goodTuples G V a q
  have hbpos : 0 < b := bOf_pos ha
  have hsum_eq : ∑ S ∈ G.powersetCard q, #(poolInter V S) =
      ∑ x : U, (degree G V x).choose q := card_poolInter_choose_sum G V q
  have hfac : q.factorial * ∑ S ∈ G.powersetCard q, #(poolInter V S) ≥
      ∑ x : U, (excess (degree G V x) q) ^ q := by
    rw [hsum_eq, Finset.mul_sum]
    exact sum_le_sum fun x _ => factorial_mul_choose_ge_excess_pow _ _ hq
  have hPM : Z ^ q ≤ n ^ (q - 1) * ∑ x : U, (excess (degree G V x) q) ^ q := by
    have := pow_sum_le_card_mul_sum_pow_nat (univ : Finset U)
      (fun x => excess (degree G V x) q) q hq
    simpa [Z, n, card_univ] using this
  have hexc : 2 * a * Z ≥ g * n := by
    simpa [Z, g, n] using sum_excess_lower G V a q ha hq hPool (by simpa [g] using hg)
  have hZpow : (2 * a) ^ q * Z ^ q ≥ (g * n) ^ q := by
    have h2 : (2 * a * Z) ^ q ≥ (g * n) ^ q := Nat.pow_le_pow_left hexc q
    rwa [mul_pow] at h2
  have hcomb : n ^ (q - 1) * q.factorial * ∑ S ∈ G.powersetCard q, #(poolInter V S) ≥ Z ^ q := by
    calc n ^ (q - 1) * q.factorial * ∑ S ∈ G.powersetCard q, #(poolInter V S)
        = n ^ (q - 1) * (q.factorial * ∑ S ∈ G.powersetCard q, #(poolInter V S)) := by ring
      _ ≥ n ^ (q - 1) * ∑ x : U, (excess (degree G V x) q) ^ q :=
          Nat.mul_le_mul_left _ hfac
      _ ≥ Z ^ q := by
          have := hPM; omega
  have hlow1 : (2 * a) ^ q * n ^ (q - 1) * q.factorial *
      ∑ S ∈ G.powersetCard q, #(poolInter V S) ≥ g ^ q * n ^ q := by
    calc (2 * a) ^ q * n ^ (q - 1) * q.factorial * ∑ S ∈ G.powersetCard q, #(poolInter V S)
        = (2 * a) ^ q * (n ^ (q - 1) * q.factorial * ∑ S ∈ G.powersetCard q, #(poolInter V S)) := by ring
      _ ≥ (2 * a) ^ q * Z ^ q := Nat.mul_le_mul_left _ hcomb
      _ ≥ (g * n) ^ q := hZpow
      _ = g ^ q * n ^ q := mul_pow g n q
  have hnpow : n ^ (q - 1) * n = n ^ q := by
    cases q with
    | zero => omega
    | succ q' =>
      simp only [Nat.succ_sub_succ_eq_sub, tsub_zero]
      ring
  have hlow2 : (2 * a) ^ q * q.factorial * ∑ S ∈ G.powersetCard q, #(poolInter V S) ≥
      g ^ q * n := by
    -- From hlow1: (2a)^q * n^{q-1} * q! * ∑ ≥ g^q * n^q = g^q * n^{q-1} * n
    have h := hlow1
    rw [← hnpow, ← mul_assoc] at h
    -- h: (2a)^q * (n^{q-1} * q! * ∑) ≥ g^q * (n^{q-1} * n) wait
    have h' : n ^ (q - 1) *
        ((2 * a) ^ q * q.factorial * ∑ S ∈ G.powersetCard q, #(poolInter V S)) ≥
        n ^ (q - 1) * (g ^ q * n) := by
      calc n ^ (q - 1) * ((2 * a) ^ q * q.factorial * ∑ S ∈ G.powersetCard q, #(poolInter V S))
          = (2 * a) ^ q * n ^ (q - 1) * q.factorial * ∑ S ∈ G.powersetCard q, #(poolInter V S) := by ring
        _ ≥ g ^ q * n ^ q := hlow1
        _ = n ^ (q - 1) * (g ^ q * n) := by rw [← hnpow]; ring
    exact Nat.le_of_mul_le_mul_left h' (pow_pos (by omega : 0 < n) _)
  have hb_eq : b = 2 * (2 * a) ^ q := by simp only [b, bOf]; ring
  have hlow3 : b * q.factorial * ∑ S ∈ G.powersetCard q, #(poolInter V S) ≥
      2 * g ^ q * n := by
    rw [hb_eq]
    calc 2 * (2 * a) ^ q * q.factorial * ∑ S ∈ G.powersetCard q, #(poolInter V S)
        = 2 * ((2 * a) ^ q * q.factorial * ∑ S ∈ G.powersetCard q, #(poolInter V S)) := by ring
      _ ≥ 2 * (g ^ q * n) := Nat.mul_le_mul_left _ hlow2
      _ = 2 * g ^ q * n := by ring
  have hgood_sub : good ⊆ G.powersetCard q := filter_subset _ _
  have hupper : b * ∑ S ∈ G.powersetCard q, #(poolInter V S) ≤
      b * #good * n + g.choose q * n := by
    have hunion : good ∪ (G.powersetCard q \ good) = G.powersetCard q :=
      union_sdiff_of_subset hgood_sub
    rw [← hunion, sum_union (disjoint_sdiff (s := good) (t := G.powersetCard q)), mul_add]
    have hG : b * ∑ S ∈ good, #(poolInter V S) ≤ b * #good * n := by
      have : ∑ S ∈ good, #(poolInter V S) ≤ #good * n := by
        calc ∑ S ∈ good, #(poolInter V S)
            ≤ ∑ S ∈ good, n := sum_le_sum fun _ _ => le_card_univ _
          _ = #good * n := by simp [sum_const]
      calc b * ∑ S ∈ good, #(poolInter V S)
          ≤ b * (#good * n) := Nat.mul_le_mul_left _ this
        _ = b * #good * n := by ring
    have hB : b * ∑ S ∈ G.powersetCard q \ good, #(poolInter V S) ≤ g.choose q * n := by
      have hterm : ∀ S ∈ G.powersetCard q \ good, b * #(poolInter V S) < n := by
        intro S hS
        have hSp : S ∈ G.powersetCard q := (mem_sdiff.mp hS).1
        have hng : S ∉ good := (mem_sdiff.mp hS).2
        have hnot : ¬ (b * #(poolInter V S) ≥ n) := by
          change ¬ (S ∈ {S' ∈ G.powersetCard q | b * #(poolInter V S') ≥ n}) at hng
          simpa [mem_filter, hSp] using hng
        exact Nat.lt_of_not_ge hnot
      rw [mul_sum]
      have h1 : ∑ S ∈ G.powersetCard q \ good, b * #(poolInter V S) ≤
          #(G.powersetCard q \ good) * n := by
        calc ∑ S ∈ G.powersetCard q \ good, b * #(poolInter V S)
            ≤ ∑ S ∈ G.powersetCard q \ good, n :=
              sum_le_sum fun S hS => Nat.le_of_lt (hterm S hS)
          _ = #(G.powersetCard q \ good) * n := by simp [sum_const]
      have h3 : #(G.powersetCard q \ good) ≤ g.choose q := by
        calc #(G.powersetCard q \ good)
            ≤ #(G.powersetCard q) := card_le_card sdiff_subset
          _ = g.choose q := by simpa [g] using card_powersetCard q G
      exact le_trans h1 (Nat.mul_le_mul_right n h3)
    exact Nat.add_le_add hG hB
  have hupper2 : b * q.factorial * ∑ S ∈ G.powersetCard q, #(poolInter V S) ≤
      b * q.factorial * #good * n + g ^ q * n := by
    have h1 := Nat.mul_le_mul_left q.factorial hupper
    have h3 : q.factorial * g.choose q * n ≤ g ^ q * n :=
      Nat.mul_le_mul_right n (factorial_mul_choose_le_pow g q)
    calc b * q.factorial * ∑ S ∈ G.powersetCard q, #(poolInter V S)
        = q.factorial * (b * ∑ S ∈ G.powersetCard q, #(poolInter V S)) := by ring
      _ ≤ q.factorial * (b * #good * n + g.choose q * n) := h1
      _ = b * q.factorial * #good * n + q.factorial * g.choose q * n := by ring
      _ ≤ b * q.factorial * #good * n + g ^ q * n := Nat.add_le_add_left h3 _
  have hcmp : 2 * g ^ q * n ≤ b * q.factorial * #good * n + g ^ q * n :=
    le_trans hlow3 hupper2
  have hfinal : g ^ q * n ≤ b * q.factorial * #good * n := by
    have : g ^ q * n + g ^ q * n ≤ b * q.factorial * #good * n + g ^ q * n := by
      convert hcmp using 1; ring
    exact Nat.le_of_add_le_add_right this
  have hout : g ^ q ≤ b * q.factorial * #good :=
    Nat.le_of_mul_le_mul_right hfinal (by omega : 0 < n)
  -- goal: b * q! * #good ≥ g^q
  simpa [b, g, good, mul_assoc, mul_left_comm, mul_comm] using hout

end E624R9

namespace Erdos624

open Finset

theorem dense_pool_intersection_cleared
    {U C : Type*} [Fintype U] [DecidableEq U] [DecidableEq C]
    (G : Finset C) (V : C → Finset U) (a q : ℕ)
    (ha : 1 ≤ a) (hq : 1 ≤ q) (hn : 1 ≤ Fintype.card U)
    (hPool : ∀ u ∈ G, a * #(V u) ≥ Fintype.card U)
    (hg : 2 * a * (q - 1) ≤ #G) :
    let b := 2 ^ (q + 1) * a ^ q
    let poolInter := fun (S : Finset C) =>
      (if h : S.Nonempty then S.inf' h V else (univ : Finset U))
    let good := {S ∈ G.powersetCard q | b * #(poolInter S) ≥ Fintype.card U}
    b * q.factorial * #good ≥ (#G) ^ q := by
  change E624R9.bOf a q * q.factorial * #(E624R9.goodTuples G V a q) ≥ (#G) ^ q
  exact E624R9.dense_pool_intersection G V a q ha hq hn hPool hg

end Erdos624

open Finset

theorem solution
    {U C : Type*} [Fintype U] [DecidableEq U] [DecidableEq C]
    (G : Finset C) (V : C → Finset U) (a q : ℕ)
    (ha : 1 ≤ a) (hq : 1 ≤ q) (hn : 1 ≤ Fintype.card U)
    (hPool : ∀ u ∈ G, a * #(V u) ≥ Fintype.card U)
    (hg : 2 * a * (q - 1) ≤ #G) :
    let b := 2 ^ (q + 1) * a ^ q
    let poolInter := fun (S : Finset C) =>
      (if h : S.Nonempty then S.inf' h V else (univ : Finset U))
    let good := {S ∈ G.powersetCard q | b * #(poolInter S) ≥ Fintype.card U}
    b * q.factorial * #good ≥ (#G) ^ q :=
  Erdos624.dense_pool_intersection_cleared G V a q ha hq hn hPool hg

#print axioms solution
