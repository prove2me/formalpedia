-- Prove2me | solution 1 for FixpNash.Bubelis.v2_pos_v3_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T11:41:44.685998+00:00
-- url     : https://prove2.me/submissions/1b5da390-32e2-4e42-9c4f-1e01fcec5877

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_FixpNash_Bubelis_Gadget


namespace GTBub
open FixpNash.Bubelis Finset

variable {m : ℕ}

def mk (a : Fin 2) (b c : Fin (m + 1)) : ∀ p, Strat m p
  | .primary => a
  | .aux2 => b
  | .aux3 => c

def eqv : (∀ p, Strat m p) ≃ Fin 2 × Fin (m + 1) × Fin (m + 1) where
  toFun s := (s .primary, s .aux2, s .aux3)
  invFun t := mk t.1 t.2.1 t.2.2
  left_inv s := by funext p; cases p <;> rfl
  right_inv t := rfl

theorem ep_eq (u : Player → (∀ p, Strat m p) → ℝ) (σ : ∀ p, Strat m p → ℝ) (i : Player) :
    AGT.expectedPayoff u σ i =
      ∑ a, ∑ b, ∑ c, σ .primary a * σ .aux2 b * σ .aux3 c * u i (mk a b c) := by
  unfold AGT.expectedPayoff
  rw [← (eqv (m := m)).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  have hU : (Finset.univ : Finset Player) = {.primary, .aux2, .aux3} := by
    ext p; cases p <;> simp
  change AGT.profileProb σ (mk a b c) * u i (mk a b c) = _
  unfold AGT.profileProb
  rw [hU]
  simp [mk, mul_assoc]

def delta {p : Player} (j : Strat m p) : Strat m p → ℝ := fun k => if k = j then 1 else 0

theorem delta_lottery {p : Player} (j : Strat m p) : AGT.IsLottery (delta j) :=
  ⟨fun _ => by unfold delta; split_ifs <;> norm_num, by simp [delta]⟩

theorem dev (c : Fin (m + 1) → ℝ) (x : ∀ p, Strat m p → ℝ) (hx : AGT.IsMixedNash (gadget c) x)
    (p : Player) (j : Strat m p) :
    AGT.expectedPayoff (gadget c) (Function.update x p (delta j)) p ≤
      AGT.expectedPayoff (gadget c) x p :=
  hx.2 p _ (delta_lottery j)

theorem pp1 (c : Fin (m + 1) → ℝ) (x : ∀ p, Strat m p → ℝ) (a : Fin 2) :
    AGT.expectedPayoff (gadget c) (Function.update x .primary (delta a)) .primary =
      ∑ b, ∑ k, x .aux2 b * x .aux3 k * gadget c .primary (mk a b k) := by
  rw [ep_eq, Finset.sum_eq_single a]
  · simp [delta]
  · intro a' _ ha'; simp [delta, ha']
  · simp

theorem pp2 (c : Fin (m + 1) → ℝ) (x : ∀ p, Strat m p → ℝ) (b : Fin (m + 1)) :
    AGT.expectedPayoff (gadget c) (Function.update x .aux2 (delta b)) .aux2 =
      ∑ a, ∑ k, x .primary a * x .aux3 k * gadget c .aux2 (mk a b k) := by
  rw [ep_eq]
  simp only [Function.update_self]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single b]
  · simp [delta]
  · intro a' _ ha'; simp [delta, ha']
  · simp

theorem pp3 (c : Fin (m + 1) → ℝ) (x : ∀ p, Strat m p → ℝ) (k : Fin (m + 1)) :
    AGT.expectedPayoff (gadget c) (Function.update x .aux3 (delta k)) .aux3 =
      ∑ a, ∑ b, x .primary a * x .aux2 b * gadget c .aux3 (mk a b k) := by
  rw [ep_eq]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single k]
  · simp [delta]
  · intro a' _ ha'; simp [delta, ha']
  · simp

theorem sum_scale {ι : Type*} [Fintype ι] (f : ι → ℝ) (hf : ∑ k, f k = 1) (A B : ℝ) :
    ∑ k, A * f k * B = A * B := by
  have : ∑ k, A * f k * B = A * (∑ k, f k) * B := by rw [Finset.mul_sum, Finset.sum_mul]
  rw [this, hf, mul_one]

theorem g1_eq (c : Fin (m + 1) → ℝ) (a : Fin 2) (b k : Fin (m + 1)) :
    gadget c .primary (mk a b k) = if a = 1 then c b else 0 := rfl

theorem g2_eq (c : Fin (m + 1) → ℝ) (a : Fin 2) (b k : Fin (m + 1)) :
    gadget c .aux2 (mk a b k) = if b = k then 1 else 0 := rfl

theorem g3_eq (c : Fin (m + 1) → ℝ) (a : Fin 2) (b k : Fin (m + 1)) :
    gadget c .aux3 (mk a b k) =
      (if b + 1 = k then 1 else 0) - (if a = 0 then 1 else 0) * (if b = k then 1 else 0)
        - (if a = 1 then 1 else 0) * (if k = 0 then 1 else 0) := rfl

theorem Q1_val (c : Fin (m + 1) → ℝ) (x : ∀ p, Strat m p → ℝ)
    (hlot : ∀ p, AGT.IsLottery (x p)) (a : Fin 2) :
    ∑ b, ∑ k, x .aux2 b * x .aux3 k * gadget c .primary (mk a b k) =
      if a = 1 then ∑ b, x .aux2 b * c b else 0 := by
  have h3 := (hlot .aux3).2
  simp only [g1_eq]
  by_cases ha : a = 1
  · simp only [if_pos ha]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [sum_scale (x .aux3) h3]
  · simp [ha]

theorem ep1_val (c : Fin (m + 1) → ℝ) (x : ∀ p, Strat m p → ℝ)
    (hlot : ∀ p, AGT.IsLottery (x p)) :
    AGT.expectedPayoff (gadget c) x .primary = x .primary 1 * ∑ b, x .aux2 b * c b := by
  have h3 := (hlot .aux3).2
  rw [ep_eq, Fin.sum_univ_two]
  simp only [g1_eq]
  simp
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [sum_scale (x .aux3) h3, mul_assoc]

theorem Q2_val (c : Fin (m + 1) → ℝ) (x : ∀ p, Strat m p → ℝ)
    (hlot : ∀ p, AGT.IsLottery (x p)) (b : Fin (m + 1)) :
    ∑ a, ∑ k, x .primary a * x .aux3 k * gadget c .aux2 (mk a b k) = x .aux3 b := by
  have h1 := (hlot .primary).2
  simp only [g2_eq, mul_ite, mul_one, mul_zero]
  simp [Finset.sum_ite_eq, ← Finset.sum_mul, h1]

theorem ep2_val (c : Fin (m + 1) → ℝ) (x : ∀ p, Strat m p → ℝ)
    (hlot : ∀ p, AGT.IsLottery (x p)) :
    AGT.expectedPayoff (gadget c) x .aux2 = ∑ b, x .aux2 b * x .aux3 b := by
  have h1 := (hlot .primary).2
  rw [ep_eq]
  simp only [g2_eq, mul_ite, mul_one, mul_zero]
  simp [Finset.sum_ite_eq]
  rw [Fin.sum_univ_two] at h1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  calc _ = (x .primary 0 + x .primary 1) * (x .aux2 b * x .aux3 b) := by ring
    _ = _ := by rw [h1, one_mul]

theorem Q3_val (c : Fin (m + 1) → ℝ) (x : ∀ p, Strat m p → ℝ)
    (hlot : ∀ p, AGT.IsLottery (x p)) (k : Fin (m + 1)) :
    ∑ a, ∑ b, x .primary a * x .aux2 b * gadget c .aux3 (mk a b k) =
      x .aux2 (k - 1) - x .primary 0 * x .aux2 k - x .primary 1 * (if k = 0 then 1 else 0) := by
  have h2 := (hlot .aux2).2
  have h1 := (hlot .primary).2
  rw [Fin.sum_univ_two] at h1
  have hA : ∑ b, x .aux2 b * (if b + 1 = k then (1:ℝ) else 0) = x .aux2 (k - 1) := by
    have : ∀ b : Fin (m + 1), (b + 1 = k) ↔ (b = k - 1) := fun b => (eq_sub_iff_add_eq).symm
    simp only [this]
    simp
  rw [Fin.sum_univ_two]
  simp only [g3_eq]
  simp
  have hB : ∑ b, x .aux2 b * (if b = k then (1:ℝ) else 0) = x .aux2 k := by simp
  have e1 : ∑ b, x .primary 0 * x .aux2 b *
      ((if b + 1 = k then (1:ℝ) else 0) - if b = k then 1 else 0) =
      x .primary 0 * (x .aux2 (k - 1) - x .aux2 k) := by
    rw [← hA, ← hB, ← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  have e2 : ∑ b, x .primary 1 * x .aux2 b *
      ((if b + 1 = k then (1:ℝ) else 0) - if k = 0 then 1 else 0) =
      x .primary 1 * (x .aux2 (k - 1) - if k = 0 then 1 else 0) := by
    have : ∀ b, x .primary 1 * x .aux2 b *
        ((if b + 1 = k then (1:ℝ) else 0) - if k = 0 then 1 else 0) =
        x .primary 1 * (x .aux2 b * if b + 1 = k then (1:ℝ) else 0) -
          (x .primary 1 * if k = 0 then (1:ℝ) else 0) * x .aux2 b := fun b => by ring
    simp only [this]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hA, h2]
    ring
  rw [e1, e2]
  split_ifs <;> linear_combination (x .aux2 (k - 1)) * h1

/-- the payoff of the pure strategy `k` of player 3 -/
noncomputable def U (x : ∀ p, Strat m p → ℝ) (k : Fin (m + 1)) : ℝ :=
  x .aux2 (k - 1) - x .primary 0 * x .aux2 k - x .primary 1 * (if k = 0 then 1 else 0)

theorem ep3_val (c : Fin (m + 1) → ℝ) (x : ∀ p, Strat m p → ℝ)
    (hlot : ∀ p, AGT.IsLottery (x p)) :
    AGT.expectedPayoff (gadget c) x .aux3 = ∑ k, x .aux3 k * U x k := by
  rw [ep_eq]
  have e : ∀ a : Fin 2, ∑ b, ∑ k, x .primary a * x .aux2 b * x .aux3 k * gadget c .aux3 (mk a b k) =
      ∑ k, ∑ b, x .primary a * x .aux2 b * x .aux3 k * gadget c .aux3 (mk a b k) :=
    fun a => Finset.sum_comm
  simp only [e]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  have := Q3_val c x hlot k
  unfold U
  rw [← this, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

theorem support_eq {ι : Type*} [Fintype ι] (p f : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (hf : ∀ i, f i ≤ ∑ i, p i * f i) (i : ι) (hi : 0 < p i) :
    f i = ∑ i, p i * f i := by
  set v := ∑ i, p i * f i with hv
  have h0 : ∑ i, p i * (v - f i) = 0 := by
    simp only [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hs, ← hv]; simp
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ p i * (v - f i) := fun i _ =>
    mul_nonneg (hp i) (sub_nonneg.2 (hf i))
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0 i (Finset.mem_univ _)
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h hi.ne'
  · linarith

theorem U_sum (x : ∀ p, Strat m p → ℝ) (hlot : ∀ p, AGT.IsLottery (x p)) :
    ∑ k, U x k = 0 := by
  have h1 := (hlot .primary).2
  rw [Fin.sum_univ_two] at h1
  have h2 := (hlot .aux2).2
  unfold U
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have a1 : ∑ k : Fin (m + 1), x .aux2 (k - 1) = 1 := by
    rw [← h2]
    exact Equiv.sum_comp (Equiv.subRight (1 : Fin (m + 1))) (fun k => x .aux2 k)
  rw [a1, ← Finset.mul_sum, ← Finset.mul_sum, h2]
  simp
  linarith

theorem ne_aux2 (c : Fin (m + 1) → ℝ) (x : ∀ p, Strat m p → ℝ)
    (hx : AGT.IsMixedNash (gadget c) x) (j : Fin (m + 1)) :
    x .aux3 j ≤ ∑ b, x .aux2 b * x .aux3 b := by
  have hlot : ∀ p, AGT.IsLottery (x p) := hx.1
  have := dev c x hx .aux2 j
  rw [pp2, Q2_val c x hlot, ep2_val c x hlot] at this
  exact this

theorem ne_aux3 (c : Fin (m + 1) → ℝ) (x : ∀ p, Strat m p → ℝ)
    (hx : AGT.IsMixedNash (gadget c) x) (k : Fin (m + 1)) :
    U x k ≤ ∑ k, x .aux3 k * U x k := by
  have hlot : ∀ p, AGT.IsLottery (x p) := hx.1
  have := dev c x hx .aux3 k
  rw [pp3, Q3_val c x hlot, ep3_val c x hlot] at this
  exact this

theorem v2_pos (c : Fin (m + 1) → ℝ) (x : ∀ p, Strat m p → ℝ)
    (hx : AGT.IsMixedNash (gadget c) x) : 0 < ∑ b, x .aux2 b * x .aux3 b := by
  have hlot : ∀ p, AGT.IsLottery (x p) := hx.1
  have := Finset.sum_le_sum (s := Finset.univ) (fun j _ => ne_aux2 c x hx j)
  rw [(hlot .aux3).2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  push_cast at this
  by_contra hneg
  rw [not_lt] at hneg
  nlinarith

theorem v3_nonneg (c : Fin (m + 1) → ℝ) (x : ∀ p, Strat m p → ℝ)
    (hx : AGT.IsMixedNash (gadget c) x) : 0 ≤ ∑ k, x .aux3 k * U x k := by
  have hlot : ∀ p, AGT.IsLottery (x p) := hx.1
  have := Finset.sum_le_sum (s := Finset.univ) (fun j _ => ne_aux3 c x hx j)
  rw [U_sum x hlot, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  push_cast at this
  by_contra hneg
  rw [not_le] at hneg
  nlinarith

open Fin.NatCast in
theorem U_zero (c : Fin (m + 1) → ℝ) (x : ∀ p, Strat m p → ℝ)
    (hx : AGT.IsMixedNash (gadget c) x) (k : Fin (m + 1)) : U x k = 0 := by
  have hlot : ∀ p, AGT.IsLottery (x p) := hx.1
  have h2pos := v2_pos c x hx
  have hv3nn := v3_nonneg c x hx
  have hv3z : ∑ k, x .aux3 k * U x k = 0 := by
    by_contra hne
    have hpos : 0 < ∑ k, x .aux3 k * U x k := lt_of_le_of_ne hv3nn (Ne.symm hne)
    have step : ∀ k, 0 < x .aux3 k → 0 < x .aux3 (k - 1) := by
      intro k hk
      have e := support_eq (x .aux3) (U x) (fun i => (hlot .aux3).1 i) (hlot .aux3).2
        (ne_aux3 c x hx) k hk
      have hU : 0 < x .aux2 (k - 1) := by
        have n1 := (hlot .primary).1 0
        have n2 := (hlot .primary).1 1
        have n3 := (hlot .aux2).1 k
        have n4 : 0 ≤ x .primary 1 * (if k = 0 then (1:ℝ) else 0) :=
          mul_nonneg n2 (by split_ifs <;> norm_num)
        have n5 := mul_nonneg n1 n3
        have hUk : 0 < U x k := by rw [e]; exact hpos
        unfold U at hUk
        linarith
      have e2 := support_eq (x .aux2) (x .aux3) (hlot .aux2).1 (hlot .aux2).2
        (ne_aux2 c x hx) (k - 1) hU
      rw [e2]; exact h2pos
    obtain ⟨k0, hk0⟩ : ∃ k0, 0 < x .aux3 k0 := by
      by_contra hno
      push Not at hno
      have := Finset.sum_nonpos (s := Finset.univ) (fun i _ => hno i)
      linarith [(hlot .aux3).2]
    have iter : ∀ n : ℕ, 0 < x .aux3 (k0 - (n : Fin (m + 1))) := by
      intro n
      induction n with
      | zero => simpa using hk0
      | succ n ih =>
        have := step _ ih
        rwa [Nat.cast_succ, sub_add_eq_sub_sub]
    have all : ∀ j, 0 < x .aux3 j := by
      intro j
      have := iter (k0 - j).val
      rwa [Fin.cast_val_eq_self, sub_sub_cancel] at this
    have allU : ∀ k, U x k = ∑ k, x .aux3 k * U x k := fun k =>
      support_eq (x .aux3) (U x) (fun i => (hlot .aux3).1 i) (hlot .aux3).2
        (ne_aux3 c x hx) k (all k)
    have hs : ∑ k, U x k = ((m : ℝ) + 1) * ∑ k, x .aux3 k * U x k := by
      rw [Finset.sum_congr rfl (fun k _ => allU k)]
      simp
    rw [U_sum x hlot] at hs
    have : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    nlinarith
  have hle : ∀ k, U x k ≤ 0 := fun k => hv3z ▸ ne_aux3 c x hx k
  exact (Finset.sum_eq_zero_iff_of_nonpos (fun k _ => hle k)).1 (U_sum x hlot) k
    (Finset.mem_univ _)

open Fin.NatCast in
theorem aux2_form (c : Fin (m + 1) → ℝ) (x : ∀ p, Strat m p → ℝ)
    (hx : AGT.IsMixedNash (gadget c) x) (j : Fin (m + 1)) :
    x .aux2 j = x .primary 0 ^ (m - (j : ℕ)) / ∑ i ∈ range (m + 1), x .primary 0 ^ i := by
  have hlot : ∀ p, AGT.IsLottery (x p) := hx.1
  set ξ := x .primary 0 with hξ
  have step : ∀ n : ℕ, n < m →
      x .aux2 (n : Fin (m + 1)) = ξ * x .aux2 ((n + 1 : ℕ) : Fin (m + 1)) := by
    intro n hn
    have h := U_zero c x hx ((n + 1 : ℕ) : Fin (m + 1))
    unfold U at h
    have hne : ¬ (((n + 1 : ℕ) : Fin (m + 1)) = 0) := by
      intro h0
      have := congrArg Fin.val h0
      rw [Fin.val_natCast, Nat.mod_eq_of_lt (by omega : n + 1 < m + 1)] at this
      simp at this
    have hsub : ((n + 1 : ℕ) : Fin (m + 1)) - 1 = (n : Fin (m + 1)) := by
      rw [Nat.cast_succ, add_sub_cancel_right]
    rw [if_neg hne, hsub] at h
    linarith
  have key : ∀ d : ℕ, d ≤ m →
      x .aux2 ((m - d : ℕ) : Fin (m + 1)) = ξ ^ d * x .aux2 (m : Fin (m + 1)) := by
    intro d
    induction d with
    | zero => intro _; simp
    | succ d ih =>
      intro hd
      rw [step (m - (d + 1)) (by omega)]
      have : m - (d + 1) + 1 = m - d := by omega
      rw [this, ih (by omega)]; ring
  have hj : ∀ j : Fin (m + 1), x .aux2 j = ξ ^ (m - (j : ℕ)) * x .aux2 (m : Fin (m + 1)) := by
    intro j
    have hjm := j.isLt
    have := key (m - (j : ℕ)) (by omega)
    rw [show m - (m - (j : ℕ)) = (j : ℕ) by omega, Fin.cast_val_eq_self] at this
    exact this
  have hsum := (hlot .aux2).2
  rw [Finset.sum_congr rfl (fun j _ => hj j), ← Finset.sum_mul] at hsum
  have hS : ∑ j : Fin (m + 1), ξ ^ (m - (j : ℕ)) = ∑ i ∈ range (m + 1), ξ ^ i := by
    rw [Fin.sum_univ_eq_sum_range (fun j => ξ ^ (m - j)) (m + 1)]
    have := Finset.sum_range_reflect (fun i => ξ ^ i) (m + 1)
    simpa using this
  rw [hS] at hsum
  have hS0 : ∑ i ∈ range (m + 1), ξ ^ i ≠ 0 := by
    intro h0; rw [h0] at hsum; simp at hsum
  rw [hj j, eq_div_iff hS0]
  linear_combination ξ ^ (m - (j : ℕ)) * hsum

theorem sum_x2_c (c : Fin (m + 1) → ℝ) (x : ∀ p, Strat m p → ℝ)
    (hx : AGT.IsMixedNash (gadget c) x) :
    ∑ b, x .aux2 b * c b = poly c (x .primary 0) / ∑ i ∈ range (m + 1), x .primary 0 ^ i := by
  rw [poly, Finset.sum_div]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [aux2_form c x hx b]; ring

end GTBub

open FixpNash.Bubelis in
theorem solution {m : ℕ} (c : Fin (m + 1) → ℝ) (x : ∀ p, Strat m p → ℝ)
    (hx : AGT.IsMixedNash (gadget c) x) :
    0 < AGT.expectedPayoff (gadget c) x .aux2 ∧ 0 ≤ AGT.expectedPayoff (gadget c) x .aux3 := by
  have hlot : ∀ p, AGT.IsLottery (x p) := hx.1
  refine ⟨?_, ?_⟩
  · rw [GTBub.ep2_val c x hlot]; exact GTBub.v2_pos c x hx
  · rw [GTBub.ep3_val c x hlot]; exact GTBub.v3_nonneg c x hx
