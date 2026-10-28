-- Prove2me | solution 1 for Erdos624.lower_layer_band_witnesses
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-25T19:36:49.384409+00:00
-- url     : https://prove2.me/submissions/6e7e1fde-1b3c-4905-9da8-f652c7bc7846

import Mathlib
open Finset

namespace E624R14L
open Finset

lemma card_filter_powerset_Icc {U : Type*} [DecidableEq U] (Z : Finset U) (lo hi : ℕ) :
    #(Z.powerset.filter (fun A => lo ≤ #A ∧ #A ≤ hi)) = ∑ a ∈ Icc lo hi, (#Z).choose a := by
  have : Z.powerset.filter (fun A => lo ≤ #A ∧ #A ≤ hi) =
      (Icc lo hi).biUnion (fun a => Z.powersetCard a) := by
    ext A
    simp only [mem_filter, mem_powerset, mem_biUnion, mem_Icc, mem_powersetCard]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨#A, ⟨h2, h3⟩, h1, rfl⟩
    · rintro ⟨a, ⟨h2, h3⟩, h1, rfl⟩; exact ⟨h1, h2, h3⟩
  rw [this, card_biUnion]
  · exact sum_congr rfl fun a _ => card_powersetCard a Z
  · intro a _ c _ hac
    rw [Function.onFun, disjoint_left]
    intro A hA hA'
    rw [mem_powersetCard] at hA hA'
    exact hac (hA.2.symm.trans hA'.2)

theorem layer {U : Type*} [DecidableEq U] {C : Type*} [Fintype C] [DecidableEq C]
    (L : Finset U → Finset C) (b k h : ℕ) (hb : ∀ A, #(L A) ≤ b) (hh : 1 ≤ h)
    (Z : Finset U) (hZ : #Z = k + 1)
    (hcov : ∀ x ∈ Z, ∀ u : C, ∃ A ⊆ Z.erase x, u ∈ L A) :
    3 * (Fintype.card C - #((Z.powerset.filter (fun A => #A < h)).biUnion L)) ≤
      b * (∑ a ∈ Icc h k, (k + 1).choose a + ∑ a ∈ Icc h ((k + 1) / 2), (k + 1).choose a) := by
  classical
  set P := (Z.powerset.filter (fun A => #A < h)).biUnion L with hP
  set M := (univ : Finset C).filter (fun u => u ∉ P) with hM
  have hMcard : #M = Fintype.card C - #P := by
    rw [hM, filter_not, card_sdiff_of_subset (by simp), card_univ]
    simp
  set Lay := Z.powerset.filter (fun A => h ≤ #A ∧ #A ≤ k) with hLay
  set Sm := Z.powerset.filter (fun A => h ≤ #A ∧ #A ≤ (k + 1) / 2) with hSm
  have hLayc : #Lay = ∑ a ∈ Icc h k, (k + 1).choose a := by
    rw [hLay, card_filter_powerset_Icc, hZ]
  have hSmc : #Sm = ∑ a ∈ Icc h ((k + 1) / 2), (k + 1).choose a := by
    rw [hSm, card_filter_powerset_Icc, hZ]
  set occ := fun u => Lay.filter (fun A => u ∈ L A) with hocc
  -- witnesses of colours in M lie in the layer range
  have hin : ∀ u ∈ M, ∀ A ⊆ Z, #A ≤ k → u ∈ L A → A ∈ occ u := by
    intro u hu A hAZ hAk huA
    rw [hM, mem_filter] at hu
    have : h ≤ #A := by
      by_contra hc
      apply hu.2
      rw [hP, mem_biUnion]
      exact ⟨A, mem_filter.2 ⟨mem_powerset.2 hAZ, by omega⟩, huA⟩
    simp only [hocc, hLay, mem_filter, mem_powerset]
    exact ⟨⟨hAZ, this, hAk⟩, huA⟩
  have hface : ∀ u ∈ M, ∀ x ∈ Z, ∃ A ∈ occ u, x ∉ A := by
    intro u hu x hx
    obtain ⟨A, hAZ, huA⟩ := hcov x hx u
    have hAk : #A ≤ k := by
      have := card_le_card hAZ; rw [card_erase_of_mem hx, hZ] at this; omega
    exact ⟨A, hin u hu A (hAZ.trans (erase_subset _ _)) hAk huA,
      fun h' => by have := hAZ h'; simp at this⟩
  have hocc_sub : ∀ u, ∀ A ∈ occ u, A ⊆ Z ∧ h ≤ #A := by
    intro u A hA
    simp only [hocc, hLay, mem_filter, mem_powerset] at hA
    exact ⟨hA.1.1, hA.1.2.1⟩
  have hkey : ∀ u ∈ M, 3 ≤ #(occ u) + (if ∃ A ∈ Sm, u ∈ L A then 1 else 0) := by
    intro u hu
    obtain ⟨x, hx⟩ : Z.Nonempty := card_pos.1 (by omega)
    obtain ⟨A1, hA1, hxA1⟩ := hface u hu x hx
    obtain ⟨y, hy⟩ : A1.Nonempty := card_pos.1 (by have := (hocc_sub u A1 hA1).2; omega)
    obtain ⟨A2, hA2, hyA2⟩ := hface u hu y ((hocc_sub u A1 hA1).1 hy)
    have h12 : A1 ≠ A2 := fun e => hyA2 (e ▸ hy)
    by_cases hdis : Disjoint A1 A2
    · have hsz : #A1 + #A2 ≤ k + 1 := by
        rw [← card_union_of_disjoint hdis, ← hZ]
        exact card_le_card (union_subset (hocc_sub u A1 hA1).1 (hocc_sub u A2 hA2).1)
      have hsmall : ∃ A ∈ Sm, u ∈ L A := by
        by_cases hc : #A1 ≤ (k + 1) / 2
        · refine ⟨A1, ?_, (mem_filter.1 hA1).2⟩
          simp only [hSm, mem_filter, mem_powerset]
          exact ⟨(hocc_sub u A1 hA1).1, (hocc_sub u A1 hA1).2, hc⟩
        · refine ⟨A2, ?_, (mem_filter.1 hA2).2⟩
          simp only [hSm, mem_filter, mem_powerset]
          exact ⟨(hocc_sub u A2 hA2).1, (hocc_sub u A2 hA2).2, by omega⟩
      rw [if_pos hsmall]
      have : 2 ≤ #(occ u) := by
        have : ({A1, A2} : Finset (Finset U)) ⊆ occ u := by
          intro A hA; rw [mem_insert, mem_singleton] at hA
          rcases hA with rfl | rfl <;> assumption
        have := card_le_card this; rw [card_pair h12] at this; exact this
      omega
    · rw [not_disjoint_iff] at hdis
      obtain ⟨z, hz1, hz2⟩ := hdis
      obtain ⟨A3, hA3, hzA3⟩ := hface u hu z ((hocc_sub u A1 hA1).1 hz1)
      have h13 : A1 ≠ A3 := fun e => hzA3 (e ▸ hz1)
      have h23 : A2 ≠ A3 := fun e => hzA3 (e ▸ hz2)
      have : ({A1, A2, A3} : Finset (Finset U)) ⊆ occ u := by
        intro A hA; simp only [mem_insert, mem_singleton] at hA
        rcases hA with rfl | rfl | rfl <;> assumption
      have := card_le_card this
      rw [card_insert_of_notMem (by simp [h12, h13]), card_pair h23] at this
      omega
  -- capacity counts
  have hsumocc : ∑ u ∈ M, #(occ u) ≤ b * #Lay := by
    have h1 : ∑ u ∈ M, #(occ u) = ∑ A ∈ Lay, #(M.filter (fun u => u ∈ L A)) := by
      simp only [hocc, card_filter]
      exact sum_comm
    rw [h1]
    calc ∑ A ∈ Lay, #(M.filter (fun u => u ∈ L A)) ≤ ∑ A ∈ Lay, #(L A) :=
          sum_le_sum fun A _ => card_le_card fun u hu => (mem_filter.1 hu).2
      _ ≤ ∑ _A ∈ Lay, b := sum_le_sum fun A _ => hb A
      _ = b * #Lay := by rw [sum_const, smul_eq_mul, mul_comm]
  have hsmallcnt : ∑ u ∈ M, (if ∃ A ∈ Sm, u ∈ L A then 1 else 0) ≤ b * #Sm := by
    rw [← card_filter]
    calc #(M.filter (fun u => ∃ A ∈ Sm, u ∈ L A)) ≤ #(Sm.biUnion L) := by
          apply card_le_card
          intro u hu
          obtain ⟨A, hA, huA⟩ := (mem_filter.1 hu).2
          exact mem_biUnion.2 ⟨A, hA, huA⟩
      _ ≤ ∑ A ∈ Sm, #(L A) := card_biUnion_le
      _ ≤ ∑ _A ∈ Sm, b := sum_le_sum fun A _ => hb A
      _ = b * #Sm := by rw [sum_const, smul_eq_mul, mul_comm]
  have hlow : ∑ _u ∈ M, 3 ≤ ∑ u ∈ M, (#(occ u) + (if ∃ A ∈ Sm, u ∈ L A then 1 else 0)) :=
    sum_le_sum hkey
  rw [sum_const, smul_eq_mul, sum_add_distrib] at hlow
  rw [← hMcard, ← hLayc, ← hSmc]
  nlinarith
end E624R14L

namespace E624R14N
open Finset

theorem cen (s : ℕ) : (2 * s).choose s ^ 2 * (3 * s + 1) ≤ 16 ^ s := by
  rw [← Nat.centralBinom_eq_two_mul_choose]
  induction s with
  | zero => simp
  | succ s ih =>
    have h := Nat.succ_mul_centralBinom_succ s
    set c := Nat.centralBinom s
    set c' := Nat.centralBinom (s + 1)
    have key : (s + 1) ^ 2 * (c' ^ 2 * (3 * (s + 1) + 1)) ≤ (s + 1) ^ 2 * 16 ^ (s + 1) := by
      have e : (s + 1) ^ 2 * (c' ^ 2 * (3 * (s + 1) + 1)) =
          4 * (2 * s + 1) ^ 2 * (3 * s + 4) * c ^ 2 := by
        have : ((s + 1) * c') ^ 2 = (2 * (2 * s + 1) * c) ^ 2 := by rw [h]
        nlinarith [this]
      rw [e, pow_succ]
      have h1 : (2 * s + 1) ^ 2 * (3 * s + 4) ≤ 4 * (s + 1) ^ 2 * (3 * s + 1) := by
        nlinarith
      calc 4 * (2 * s + 1) ^ 2 * (3 * s + 4) * c ^ 2
          = 4 * ((2 * s + 1) ^ 2 * (3 * s + 4)) * c ^ 2 := by ring
        _ ≤ 4 * (4 * (s + 1) ^ 2 * (3 * s + 1)) * c ^ 2 :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h1)
        _ = 16 * (s + 1) ^ 2 * (c ^ 2 * (3 * s + 1)) := by ring
        _ ≤ 16 * (s + 1) ^ 2 * 16 ^ s := Nat.mul_le_mul_left _ ih
        _ = (s + 1) ^ 2 * (16 ^ s * 16) := by ring
    exact le_of_mul_le_mul_left key (by positivity)

/-- `Σ_{a ≤ R} C(v,a) · 3^(v-R) ≤ 4^v`. -/
lemma low_sum (v R : ℕ) (hR : R ≤ v) :
    (∑ a ∈ range (R + 1), v.choose a) * 3 ^ (v - R) ≤ 4 ^ v := by
  have h4 : (4 : ℕ) ^ v = ∑ a ∈ range (v + 1), v.choose a * 3 ^ (v - a) := by
    have := (add_pow (1 : ℕ) 3 v)
    rw [show (1 : ℕ) + 3 = 4 by norm_num] at this
    rw [this]
    refine sum_congr rfl fun a _ => by rw [one_pow, one_mul, mul_comm, Nat.cast_id]
  rw [h4, sum_mul]
  calc ∑ a ∈ range (R + 1), v.choose a * 3 ^ (v - R)
      ≤ ∑ a ∈ range (R + 1), v.choose a * 3 ^ (v - a) := by
        refine sum_le_sum fun a ha => ?_
        rw [mem_range] at ha
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
    _ ≤ ∑ a ∈ range (v + 1), v.choose a * 3 ^ (v - a) :=
        sum_le_sum_of_subset (range_subset_range.2 (by omega))

lemma exp_ineq (v : ℕ) (hv : 56 ≤ v) : 16 ^ v * 2 ^ 28 < 27 ^ v := by
  induction v, hv using Nat.le_induction with
  | base => norm_num
  | succ v _ ih =>
    rw [pow_succ 16, pow_succ 27]
    have h1 := Nat.mul_lt_mul_of_pos_right ih (show 0 < 16 by norm_num)
    have h2 : 27 ^ v * 16 ≤ 27 ^ v * 27 := Nat.mul_le_mul_left _ (by norm_num)
    calc 16 ^ v * 16 * 2 ^ 28 = 16 ^ v * 2 ^ 28 * 16 := by ring
      _ < 27 ^ v * 16 := h1
      _ ≤ 27 ^ v * 27 := h2

theorem tail (k : ℕ) (hk : 55 ≤ k) :
    64 * ∑ a ∈ range ((k + 1) / 4 + 1), (k + 1).choose a < 2 ^ k := by
  set v := k + 1 with hv
  set R := v / 4 with hR
  set w := v - R with hw
  have h4w : 3 * v ≤ 4 * w := by omega
  have hlow := low_sum v R (by omega)
  -- 2^(v+7) < 3^w
  have hpow : 2 ^ (v + 7) < 3 ^ w := by
    have a1 : (2 ^ (v + 7)) ^ 4 < (3 ^ w) ^ 4 := by
      calc (2 ^ (v + 7)) ^ 4 = 16 ^ v * 2 ^ 28 := by
            rw [← pow_mul, show (v + 7) * 4 = 4 * v + 28 by ring, pow_add, pow_mul]; norm_num
        _ < 27 ^ v := exp_ineq v (by omega)
        _ = 3 ^ (3 * v) := by rw [pow_mul]; norm_num
        _ ≤ 3 ^ (4 * w) := Nat.pow_le_pow_right (by norm_num) h4w
        _ = (3 ^ w) ^ 4 := by rw [← pow_mul, mul_comm]
    exact lt_of_pow_lt_pow_left₀ 4 (by positivity) a1
  set S := ∑ a ∈ range (R + 1), v.choose a
  have : S * 2 ^ (v + 7) < 4 ^ v := by
    rcases Nat.eq_zero_or_pos S with h0 | hpos
    · rw [h0]; simp
    · calc S * 2 ^ (v + 7) < S * 3 ^ w := Nat.mul_lt_mul_of_pos_left hpow hpos
        _ ≤ 4 ^ v := hlow
  have e4 : (4 : ℕ) ^ v = 2 ^ v * 2 ^ v := by rw [← mul_pow]; norm_num
  have e2 : (2 : ℕ) ^ (v + 7) = 2 ^ v * 128 := by rw [pow_add]; norm_num
  have e3 : (2 : ℕ) ^ v = 2 ^ k * 2 := by rw [hv, pow_succ]
  rw [e4, e2] at this
  have h5 : S * 128 < 2 ^ v := by
    have hp : 0 < 2 ^ v := by positivity
    nlinarith
  rw [e3] at h5
  omega
end E624R14N

namespace E624R14B
open Finset

lemma upper_half (k s : ℕ) (hs : k ≤ 2 * s) :
    2 * ∑ a ∈ Icc (s + 1) k, (k + 1).choose a + 1 ≤ 2 ^ (k + 1) := by
  have hrefl : ∑ a ∈ Icc (s + 1) k, (k + 1).choose a = ∑ a ∈ Icc 1 (k - s), (k + 1).choose a := by
    refine sum_nbij' (fun a => k + 1 - a) (fun a => k + 1 - a) ?_ ?_ ?_ ?_ ?_
    · intro a ha; simp only [mem_Icc, coe_Icc, Set.mem_Icc, mem_coe] at ha ⊢; omega
    · intro a ha; simp only [mem_Icc, coe_Icc, Set.mem_Icc, mem_coe] at ha ⊢; omega
    · intro a ha; simp only [mem_Icc, coe_Icc, Set.mem_Icc, mem_coe] at ha; omega
    · intro a ha; simp only [mem_Icc, coe_Icc, Set.mem_Icc, mem_coe] at ha; omega
    · intro a ha; simp only [mem_Icc] at ha; rw [Nat.choose_symm (by omega)]
  have hsub : ({0} ∪ Icc 1 (k - s)) ∪ Icc (s + 1) k ⊆ range (k + 2) := by
    intro a ha; simp only [mem_union, mem_singleton, mem_Icc, mem_range] at ha ⊢; omega
  have hd1 : Disjoint ({0} : Finset ℕ) (Icc 1 (k - s)) := by
    rw [disjoint_left]; intro a h1 h2; simp only [mem_singleton, mem_Icc] at h1 h2; omega
  have hd2 : Disjoint ({0} ∪ Icc 1 (k - s)) (Icc (s + 1) k) := by
    rw [disjoint_left]; intro a h1 h2; simp only [mem_union, mem_singleton, mem_Icc] at h1 h2; omega
  have := sum_le_sum_of_subset (f := fun a => (k + 1).choose a) hsub
  rw [sum_union hd2, sum_union hd1, Nat.sum_range_choose, sum_singleton, Nat.choose_zero_right,
    ← hrefl] at this
  omega

lemma odd_mid (s : ℕ) : (2 * s + 1).choose s ≤ 2 * (2 * s).choose s := by
  cases s with
  | zero => simp
  | succ t =>
    rw [show 2 * (t + 1) + 1 = 2 * (t + 1) + 1 from rfl, Nat.choose_succ_succ]
    have := Nat.choose_le_middle t (2 * (t + 1))
    rw [show 2 * (t + 1) / 2 = t + 1 by omega] at this
    simp only [Nat.succ_eq_add_one] at *
    omega

lemma mid_sq (k : ℕ) (hk : 1024 ≤ k) :
    (32 * (Nat.sqrt k / 32 + 2) * (k + 1).choose ((k + 1) / 2)) ^ 2 ≤ 25 * 4 ^ k := by
  set r := Nat.sqrt k / 32
  set q := Nat.sqrt k
  have hq : q * q ≤ k := Nat.sqrt_le k
  have hq32 : 32 ≤ q := Nat.le_sqrt.2 (by omega)
  have hr : 32 * r ≤ q := Nat.mul_div_le q 32
  set s := (k + 1) / 2
  have hkey : 4096 * (r + 2) ^ 2 ≤ 25 * (3 * s + 1) := by
    have h1 : 1024 * r * r ≤ k := by nlinarith
    have h2 : 512 * (32 * r) ≤ 16 * k := by nlinarith
    have hs2 : k ≤ 2 * s := by omega
    have e : 4096 * (r + 2) ^ 2 = 4 * (1024 * r * r) + 16384 * r + 16384 := by ring
    linarith
  have hc := E624R14N.cen s
  rcases Nat.even_or_odd (k + 1) with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- k + 1 = 2 s
    have hs : s = m := by omega
    have hks : k + 1 = 2 * s := by omega
    rw [hks]
    have e4 : 4 * 4 ^ k = 16 ^ s := by
      rw [show (16 : ℕ) = 4 ^ 2 by norm_num, ← pow_mul, ← pow_succ']; congr 1
    have : 4096 * (r + 2) ^ 2 * (2 * s).choose s ^ 2 ≤ 25 * 16 ^ s := by
      calc 4096 * (r + 2) ^ 2 * (2 * s).choose s ^ 2 ≤ 25 * (3 * s + 1) * (2 * s).choose s ^ 2 :=
            Nat.mul_le_mul_right _ hkey
        _ = 25 * ((2 * s).choose s ^ 2 * (3 * s + 1)) := by ring
        _ ≤ 25 * 16 ^ s := Nat.mul_le_mul_left _ hc
    rw [← e4] at this
    have e5 : 4 * (32 * (r + 2) * (2 * s).choose s) ^ 2 = 4096 * (r + 2) ^ 2 * (2 * s).choose s ^ 2 := by ring
    linarith
  · -- k = 2 s
    have hks : k = 2 * s := by omega
    rw [hks]
    have e4 : 4 ^ (2 * s) = 16 ^ s := by
      rw [show (16 : ℕ) = 4 ^ 2 by norm_num, ← pow_mul]
    rw [e4]
    have hc2 := odd_mid s
    calc (32 * (r + 2) * (2 * s + 1).choose s) ^ 2
        ≤ (32 * (r + 2) * (2 * (2 * s).choose s)) ^ 2 := by
          apply Nat.pow_le_pow_left; exact Nat.mul_le_mul_left _ hc2
      _ = 4096 * (r + 2) ^ 2 * (2 * s).choose s ^ 2 := by ring
      _ ≤ 25 * (3 * s + 1) * (2 * s).choose s ^ 2 := Nat.mul_le_mul_right _ hkey
      _ = 25 * ((2 * s).choose s ^ 2 * (3 * s + 1)) := by ring
      _ ≤ 25 * 16 ^ s := Nat.mul_le_mul_left _ hc

lemma card_biUnion_cap {U C : Type*} [DecidableEq U] [DecidableEq C] (L : Finset U → Finset C)
    (F : Finset (Finset U)) (hb : ∀ A, #(L A) ≤ 2) : #(F.biUnion L) ≤ 2 * #F := by
  calc #(F.biUnion L) ≤ ∑ A ∈ F, #(L A) := card_biUnion_le
    _ ≤ ∑ _A ∈ F, 2 := sum_le_sum fun A _ => hb A
    _ = 2 * #F := by rw [sum_const, smul_eq_mul, mul_comm]

theorem band {U : Type*} [DecidableEq U] {C : Type*} [Fintype C] [DecidableEq C]
    (L : Finset U → Finset C) (k : ℕ) (hk : 1024 ≤ k) (hC : Fintype.card C = 2 ^ k)
    (hb : ∀ A, #(L A) ≤ 2) (Z : Finset U) (hZ : #Z = k + 1)
    (hcov : ∀ x ∈ Z, ∀ u : C, ∃ A ⊆ Z.erase x, u ∈ L A) :
    2 ^ k < 8 * #((Z.powerset.filter (fun A => #A < k / 2 - Nat.sqrt k / 32)).biUnion L) ∧
    32 * #((Z.powerset.filter (fun A => #A ≤ (k + 1) / 4)).biUnion L) < 2 ^ k ∧
    3 * 2 ^ k < 32 * #((Z.powerset.filter
      (fun A => (k + 1) / 4 < #A ∧ #A < k / 2 - Nat.sqrt k / 32)).biUnion L) := by
  set r := Nat.sqrt k / 32 with hr
  set h := k / 2 - r with hh
  set s := (k + 1) / 2 with hs
  have hq32 : 32 ≤ Nat.sqrt k := Nat.le_sqrt.2 (by omega)
  have hqk : Nat.sqrt k * Nat.sqrt k ≤ k := Nat.sqrt_le k
  have hrk : 32 * r ≤ Nat.sqrt k := Nat.mul_div_le _ 32
  have hr_small : 64 * r ≤ k := by nlinarith
  have hh1 : 1 ≤ h := by omega
  have hhs : h ≤ s := by omega
  -- (M)
  set P := (Z.powerset.filter (fun A => #A < h)).biUnion L with hP
  have hlay := E624R14L.layer L 2 k h hb hh1 Z hZ hcov
  rw [hC] at hlay
  set B := ∑ a ∈ Icc h s, (k + 1).choose a with hB
  set S := ∑ a ∈ Icc h k, (k + 1).choose a with hS
  set c := (k + 1).choose s
  have hlay' : 3 * (2 ^ k - #P) ≤ 2 * (S + B) := hlay
  have hBc : B ≤ (r + 2) * c := by
    calc B ≤ ∑ _a ∈ Icc h s, c := sum_le_sum fun a _ => Nat.choose_le_middle a (k + 1)
      _ = #(Icc h s) * c := by rw [sum_const, smul_eq_mul]
      _ ≤ (r + 2) * c := Nat.mul_le_mul_right _ (by rw [Nat.card_Icc]; omega)
  have hB5 : 32 * B ≤ 5 * 2 ^ k := by
    have h1 := mid_sq k hk
    have h2 : (32 * B) ^ 2 ≤ (5 * 2 ^ k) ^ 2 := by
      calc (32 * B) ^ 2 ≤ (32 * (r + 2) * c) ^ 2 := by
            apply Nat.pow_le_pow_left; rw [mul_assoc]; exact Nat.mul_le_mul_left _ hBc
        _ ≤ 25 * 4 ^ k := h1
        _ = (5 * 2 ^ k) ^ 2 := by rw [mul_pow, ← pow_mul, mul_comm k 2, pow_mul]; norm_num
    exact (Nat.pow_le_pow_iff_left (by norm_num)).1 h2
  have hSB : S ≤ B + ∑ a ∈ Icc (s + 1) k, (k + 1).choose a := by
    have hsplit : Icc h k = Icc h s ∪ Icc (s + 1) k := by
      ext a; simp only [mem_Icc, mem_union]; omega
    have hdisj : Disjoint (Icc h s) (Icc (s + 1) k) := by
      rw [disjoint_left]; intro a h1 h2; simp only [mem_Icc] at h1 h2; omega
    rw [hS, hsplit, sum_union hdisj]
  have hU := upper_half k s (by omega)
  have hPle : #P ≤ 2 ^ k := by rw [← hC]; exact card_le_univ P
  have hM : 2 ^ k < 8 * #P := by
    have e : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
    clear_value P B S c
    omega
  -- (T)
  have hT := E624R14N.tail k (by omega)
  have hTsub : #(Z.powerset.filter (fun A => #A ≤ (k + 1) / 4)) =
      ∑ a ∈ range ((k + 1) / 4 + 1), (k + 1).choose a := by
    have := E624R14L.card_filter_powerset_Icc Z 0 ((k + 1) / 4)
    rw [hZ] at this
    have e1 : Z.powerset.filter (fun A => #A ≤ (k + 1) / 4) =
        Z.powerset.filter (fun A => 0 ≤ #A ∧ #A ≤ (k + 1) / 4) := by simp
    have e2 : Icc 0 ((k + 1) / 4) = range ((k + 1) / 4 + 1) := by
      ext a; simp only [mem_Icc, mem_range]; omega
    rw [e1, this, e2]
  have hT2 : 32 * #((Z.powerset.filter (fun A => #A ≤ (k + 1) / 4)).biUnion L) < 2 ^ k := by
    have := card_biUnion_cap L (Z.powerset.filter (fun A => #A ≤ (k + 1) / 4)) hb
    rw [hTsub] at this
    omega
  refine ⟨hM, hT2, ?_⟩
  -- (BAND)
  have hsub : P ⊆ (Z.powerset.filter (fun A => #A ≤ (k + 1) / 4)).biUnion L ∪
      (Z.powerset.filter (fun A => (k + 1) / 4 < #A ∧ #A < h)).biUnion L := by
    intro u hu
    rw [hP, mem_biUnion] at hu
    obtain ⟨A, hA, huA⟩ := hu
    rw [mem_filter] at hA
    rw [mem_union, mem_biUnion, mem_biUnion]
    by_cases hc : #A ≤ (k + 1) / 4
    · exact Or.inl ⟨A, mem_filter.2 ⟨hA.1, hc⟩, huA⟩
    · exact Or.inr ⟨A, mem_filter.2 ⟨hA.1, by omega, hA.2⟩, huA⟩
  have := (card_le_card hsub).trans (card_union_le _ _)
  omega
end E624R14B

namespace Erdos624

theorem lower_layer_band_witnesses {U : Type*} [DecidableEq U] {C : Type*} [Fintype C] [DecidableEq C]
    (L : Finset U → Finset C) (k : ℕ) (hk : 1024 ≤ k) (hC : Fintype.card C = 2 ^ k)
    (hb : ∀ A, #(L A) ≤ 2) (Z : Finset U) (hZ : #Z = k + 1)
    (hcov : ∀ x ∈ Z, ∀ u : C, ∃ A ⊆ Z.erase x, u ∈ L A) :
    2 ^ k < 8 * #((Z.powerset.filter (fun A => #A < k / 2 - Nat.sqrt k / 32)).biUnion L) ∧
    32 * #((Z.powerset.filter (fun A => #A ≤ (k + 1) / 4)).biUnion L) < 2 ^ k ∧
    3 * 2 ^ k < 32 * #((Z.powerset.filter
      (fun A => (k + 1) / 4 < #A ∧ #A < k / 2 - Nat.sqrt k / 32)).biUnion L) := by
  exact E624R14B.band L k hk hC hb Z hZ hcov

end Erdos624

open Finset

theorem solution {U : Type*} [DecidableEq U] {C : Type*} [Fintype C] [DecidableEq C]
    (L : Finset U → Finset C) (k : ℕ) (hk : 1024 ≤ k) (hC : Fintype.card C = 2 ^ k)
    (hb : ∀ A, #(L A) ≤ 2) (Z : Finset U) (hZ : #Z = k + 1)
    (hcov : ∀ x ∈ Z, ∀ u : C, ∃ A ⊆ Z.erase x, u ∈ L A) :
    2 ^ k < 8 * #((Z.powerset.filter (fun A => #A < k / 2 - Nat.sqrt k / 32)).biUnion L) ∧
    32 * #((Z.powerset.filter (fun A => #A ≤ (k + 1) / 4)).biUnion L) < 2 ^ k ∧
    3 * 2 ^ k < 32 * #((Z.powerset.filter
      (fun A => (k + 1) / 4 < #A ∧ #A < k / 2 - Nat.sqrt k / 32)).biUnion L) :=
  Erdos624.lower_layer_band_witnesses L k hk hC hb Z hZ hcov
