-- Prove2me | solution 1 for FixpNash.Bubelis.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T13:57:03.419454+00:00
-- url     : https://prove2.me/submissions/d8d111dc-7d71-45a0-90e4-395ccb696e4e

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_FixpNash_Bubelis_Gadget

set_option autoImplicit false

namespace FixpNash.Bubelis.L7Aux

open Finset FixpNash.Bubelis

/-- The pure profile `(a, b, d)`. -/
def mk {m : ℕ} (a : Fin 2) (b d : Fin (m + 1)) : ∀ p, Strat m p
  | .primary => a
  | .aux2 => b
  | .aux3 => d

def triEquiv (m : ℕ) : (Fin 2 × Fin (m + 1) × Fin (m + 1)) ≃ (∀ p, Strat m p) where
  toFun t := mk t.1 t.2.1 t.2.2
  invFun s := (s .primary, s .aux2, s .aux3)
  left_inv t := rfl
  right_inv s := by funext p; cases p <;> rfl

lemma sum_strat {m : ℕ} (g : (∀ p, Strat m p) → ℝ) :
    ∑ s, g s = ∑ a : Fin 2, ∑ b : Fin (m + 1), ∑ d : Fin (m + 1), g (mk a b d) := by
  rw [← (triEquiv m).sum_comp g, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  rfl

lemma univ_player : (Finset.univ : Finset Player) = {.primary, .aux2, .aux3} := rfl

lemma prob_mk {m : ℕ} (σ : ∀ p, Strat m p → ℝ) (a : Fin 2) (b d : Fin (m + 1)) :
    AGT.profileProb σ (mk a b d) = σ .primary a * σ .aux2 b * σ .aux3 d := by
  unfold AGT.profileProb
  rw [univ_player, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  simp only [mk]
  ring

lemma E_eq {m : ℕ} (c : Fin (m + 1) → ℝ) (σ : ∀ p, Strat m p → ℝ) (i : Player) :
    AGT.expectedPayoff (gadget c) σ i =
      ∑ a : Fin 2, ∑ b : Fin (m + 1), ∑ d : Fin (m + 1),
        σ .primary a * σ .aux2 b * σ .aux3 d * gadget c i (mk a b d) := by
  unfold AGT.expectedPayoff
  rw [sum_strat]
  simp only [prob_mk]

lemma rearr1 {m : ℕ} (P : Fin 2 → ℝ) (Q R : Fin (m + 1) → ℝ)
    (g : Fin 2 → Fin (m + 1) → Fin (m + 1) → ℝ) :
    ∑ a, ∑ b, ∑ d, P a * Q b * R d * g a b d = ∑ a, P a * (∑ b, ∑ d, Q b * R d * g a b d) := by
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  ring

lemma rearr2 {m : ℕ} (P : Fin 2 → ℝ) (Q R : Fin (m + 1) → ℝ)
    (g : Fin 2 → Fin (m + 1) → Fin (m + 1) → ℝ) :
    ∑ a, ∑ b, ∑ d, P a * Q b * R d * g a b d = ∑ b, Q b * (∑ a, ∑ d, P a * R d * g a b d) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  ring

lemma rearr3 {m : ℕ} (P : Fin 2 → ℝ) (Q R : Fin (m + 1) → ℝ)
    (g : Fin 2 → Fin (m + 1) → Fin (m + 1) → ℝ) :
    ∑ a, ∑ b, ∑ d, P a * Q b * R d * g a b d = ∑ d, R d * (∑ a, ∑ b, P a * Q b * g a b d) := by
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm), Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-- payoff of the pure strategies of the primary player -/
def U1 {m : ℕ} (c : Fin (m + 1) → ℝ) (x : ∀ p, Strat m p → ℝ) (t : Fin 2) : ℝ :=
  if t = 1 then ∑ b, x .aux2 b * c b else 0

/-- payoff of the pure strategies of player 3 -/
def U3 {m : ℕ} (x : ∀ p, Strat m p → ℝ) (d : Fin (m + 1)) : ℝ :=
  x .aux2 (d - 1) - x .primary 0 * x .aux2 d - x .primary 1 * (if d = 0 then 1 else 0)

lemma E1 {m : ℕ} (c : Fin (m + 1) → ℝ) (x : ∀ p, Strat m p → ℝ)
    (hz : ∑ d, x .aux3 d = 1) (τ : Fin 2 → ℝ) :
    AGT.expectedPayoff (gadget c) (Function.update x .primary τ) .primary =
      ∑ t, τ t * U1 c x t := by
  rw [E_eq]
  simp only [Function.update_self,
    Function.update_of_ne (show Player.aux2 ≠ Player.primary by decide),
    Function.update_of_ne (show Player.aux3 ≠ Player.primary by decide)]
  rw [rearr1]
  refine Finset.sum_congr rfl fun t _ => ?_
  congr 1
  unfold U1
  have hg : ∀ b d, gadget c .primary (mk t b d) = if t = 1 then c b else 0 := fun _ _ => rfl
  simp only [hg]
  split_ifs with ht
  · rw [Finset.sum_congr rfl fun b _ => (show ∑ d, x .aux2 b * x .aux3 d * c b
        = x .aux2 b * c b by rw [← Finset.sum_mul, ← Finset.mul_sum, hz]; ring)]
  · simp

lemma E2 {m : ℕ} (c : Fin (m + 1) → ℝ) (x : ∀ p, Strat m p → ℝ)
    (hp : x .primary 0 + x .primary 1 = 1) (τ : Fin (m + 1) → ℝ) :
    AGT.expectedPayoff (gadget c) (Function.update x .aux2 τ) .aux2 =
      ∑ t, τ t * x .aux3 t := by
  rw [E_eq]
  simp only [Function.update_self,
    Function.update_of_ne (show Player.primary ≠ Player.aux2 by decide),
    Function.update_of_ne (show Player.aux3 ≠ Player.aux2 by decide)]
  rw [rearr2]
  refine Finset.sum_congr rfl fun t _ => ?_
  congr 1
  have hg : ∀ a d, gadget c .aux2 (mk a t d) = if t = d then 1 else 0 := fun _ _ => rfl
  simp only [hg, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Fin.sum_univ_two]
  rw [← add_mul, hp, one_mul]

lemma E3 {m : ℕ} (c : Fin (m + 1) → ℝ) (x : ∀ p, Strat m p → ℝ)
    (hp : x .primary 0 + x .primary 1 = 1) (hy : ∑ b, x .aux2 b = 1) (τ : Fin (m + 1) → ℝ) :
    AGT.expectedPayoff (gadget c) (Function.update x .aux3 τ) .aux3 =
      ∑ t, τ t * U3 x t := by
  rw [E_eq]
  simp only [Function.update_self,
    Function.update_of_ne (show Player.primary ≠ Player.aux3 by decide),
    Function.update_of_ne (show Player.aux2 ≠ Player.aux3 by decide)]
  rw [rearr3]
  refine Finset.sum_congr rfl fun t _ => ?_
  congr 1
  have hg : ∀ a b, gadget c .aux3 (mk a b t) =
      (if b + 1 = t then 1 else 0) - (if a = 0 then 1 else 0) * (if b = t then 1 else 0)
        - (if a = 1 then 1 else 0) * (if t = 0 then 1 else 0) := fun _ _ => rfl
  have hshift : ∀ b : Fin (m + 1), (b + 1 = t) ↔ (b = t - 1) := fun b => eq_sub_iff_add_eq.symm
  simp only [hg, hshift, Fin.sum_univ_two, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  unfold U3
  simp only [show (0 : Fin 2) ≠ 1 by decide, if_false]
  rw [← add_mul, hp, one_mul]
  by_cases ht : t = 0
  · simp only [ht, if_true, Finset.sum_const_zero, zero_add, ← Finset.mul_sum, hy]
  · simp only [ht, if_false, Finset.sum_const_zero, add_zero, mul_zero]

lemma lot_single {β : Type*} [Fintype β] [DecidableEq β] (t : β) :
    AGT.IsLottery (fun s => if s = t then (1 : ℝ) else 0) := by
  refine ⟨fun s => ?_, by simp⟩
  show 0 ≤ (if s = t then (1 : ℝ) else 0)
  split_ifs <;> norm_num

lemma br_of {β : Type*} [Fintype β] [DecidableEq β] (σ U : β → ℝ)
    (h : ∀ τ : β → ℝ, AGT.IsLottery τ → ∑ t, τ t * U t ≤ ∑ t, σ t * U t) :
    ∀ t, U t ≤ ∑ s, σ s * U s := by
  intro t
  have := h _ (lot_single t)
  simpa [ite_mul] using this

lemma supp_of {β : Type*} [Fintype β] (σ U : β → ℝ) (hσ : AGT.IsLottery σ)
    (h : ∀ t, U t ≤ ∑ s, σ s * U s) : ∀ t, σ t * (∑ s, σ s * U s - U t) = 0 := by
  have hsum : ∑ t, σ t * (∑ s, σ s * U s - U t) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hσ.2, one_mul, sub_self]
  have hnn : ∀ t ∈ (Finset.univ : Finset β), 0 ≤ σ t * (∑ s, σ s * U s - U t) :=
    fun t _ => mul_nonneg (hσ.1 t) (sub_nonneg.2 (h t))
  intro t
  exact (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum t (Finset.mem_univ t)

lemma const_sum {β : Type*} [Fintype β] (τ U : β → ℝ) (K : ℝ) (hU : ∀ t, U t = K)
    (hτ : AGT.IsLottery τ) : ∑ t, τ t * U t = K := by
  simp only [hU, ← Finset.sum_mul, hτ.2, one_mul]

lemma sumU3 {m : ℕ} (x : ∀ p, Strat m p → ℝ)
    (hp : x .primary 0 + x .primary 1 = 1) (hy : ∑ b, x .aux2 b = 1) :
    ∑ d, U3 x d = 0 := by
  unfold U3
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, hy]
  have : ∑ d : Fin (m + 1), x .aux2 (d - 1) = ∑ d, x .aux2 d :=
    Equiv.sum_comp (Equiv.subRight (1 : Fin (m + 1))) (x .aux2)
  rw [this, hy]
  linarith

open Fin.NatCast in
/-- the structure of every Nash equilibrium -/
theorem ne_struct {m : ℕ} (c : Fin (m + 1) → ℝ) (x : ∀ p, Strat m p → ℝ)
    (hx : AGT.IsMixedNash (gadget c) x) :
    (∀ j : Fin (m + 1), x .aux2 j = x .primary 0 ^ (m - (j : ℕ)) * x .aux2 (Fin.last m)) ∧
    0 < x .aux2 (Fin.last m) ∧
    0 ≤ x .primary 1 * poly c (x .primary 0) ∧ x .primary 0 * poly c (x .primary 0) ≤ 0 ∧
    (∀ b, 0 < x .aux2 b → x .aux3 b = ∑ s, x .aux2 s * x .aux3 s) := by
  have hP := hx.1 .primary
  have hY := hx.1 .aux2
  have hZ := hx.1 .aux3
  have hp : x .primary 0 + x .primary 1 = 1 := by
    have := hP.2; rwa [Fin.sum_univ_two] at this
  have hp0 : 0 ≤ x .primary 0 := hP.1 0
  have hp1 : 0 ≤ x .primary 1 := hP.1 1
  have hy : ∑ b, x .aux2 b = 1 := hY.2
  have hz : ∑ b, x .aux3 b = 1 := hZ.2
  -- player 3
  have h3 : ∀ τ : Fin (m + 1) → ℝ, AGT.IsLottery τ →
      ∑ t, τ t * U3 x t ≤ ∑ t, x .aux3 t * U3 x t := by
    intro τ hτ
    have := hx.2 .aux3 τ hτ
    rw [E3 c x hp hy τ] at this
    have e := E3 c x hp hy (x .aux3)
    rw [Function.update_eq_self] at e
    rwa [e] at this
  have br3 := br_of _ _ h3
  have sp3 := supp_of _ _ hZ br3
  -- player 2
  have h2 : ∀ τ : Fin (m + 1) → ℝ, AGT.IsLottery τ →
      ∑ t, τ t * x .aux3 t ≤ ∑ t, x .aux2 t * x .aux3 t := by
    intro τ hτ
    have := hx.2 .aux2 τ hτ
    rw [E2 c x hp τ] at this
    have e := E2 c x hp (x .aux2)
    rw [Function.update_eq_self] at e
    rwa [e] at this
  have br2 := br_of _ _ h2
  have sp2 := supp_of _ _ hY br2
  -- player 1
  have h1 : ∀ τ : Fin 2 → ℝ, AGT.IsLottery τ →
      ∑ t, τ t * U1 c x t ≤ ∑ t, x .primary t * U1 c x t := by
    intro τ hτ
    have := hx.2 .primary τ hτ
    rw [E1 c x hz τ] at this
    have e := E1 c x hz (x .primary)
    rw [Function.update_eq_self] at e
    rwa [e] at this
  have br1 := br_of _ _ h1
  -- v3 = 0
  set v3 := ∑ s, x .aux3 s * U3 x s with hv3
  set v2 := ∑ s, x .aux2 s * x .aux3 s with hv2
  have hS := sumU3 x hp hy
  have hcard : ∑ _d : Fin (m + 1), v3 = (m + 1) * v3 := by simp
  have hv3nn : 0 ≤ v3 := by
    have := Finset.sum_le_sum (fun d (_ : d ∈ (Finset.univ : Finset (Fin (m + 1)))) => br3 d)
    rw [hS, hcard] at this
    have hm : (0 : ℝ) < m + 1 := by positivity
    nlinarith
  have hv2pos : 0 < v2 := by
    have := Finset.sum_le_sum (fun d (_ : d ∈ (Finset.univ : Finset (Fin (m + 1)))) => br2 d)
    rw [hz] at this
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    push_cast at this
    have hm : (0 : ℝ) < m + 1 := by positivity
    nlinarith
  have hv3 : v3 = 0 := by
    by_contra hne
    have hpos : 0 < v3 := lt_of_le_of_ne hv3nn (Ne.symm hne)
    have step : ∀ b, 0 < x .aux2 b → 0 < x .aux2 (b - 1) := by
      intro b hb
      have hzb : x .aux3 b = v2 := by
        have := sp2 b
        have := (mul_eq_zero.1 this).resolve_left hb.ne'
        linarith
      have hu : U3 x b = v3 := by
        have := sp3 b
        have := (mul_eq_zero.1 this).resolve_left (by rw [hzb]; exact hv2pos.ne')
        linarith
      unfold U3 at hu
      have h1' : 0 ≤ x .primary 0 * x .aux2 b := mul_nonneg hp0 hb.le
      have h2' : 0 ≤ x .primary 1 * (if b = 0 then (1 : ℝ) else 0) :=
        mul_nonneg hp1 (by split_ifs <;> norm_num)
      linarith
    obtain ⟨b, -, hb⟩ := Finset.exists_lt_of_sum_lt
      (show ∑ _i : Fin (m + 1), (0 : ℝ) < ∑ i : Fin (m + 1), x .aux2 i by rw [hy]; simp)
    have all : ∀ k : ℕ, 0 < x .aux2 (b - ((k : ℕ) : Fin (m + 1))) := by
      intro k
      induction k with
      | zero => simpa using hb
      | succ k ih =>
        have := step _ ih
        rw [Nat.cast_succ, ← sub_sub]
        exact this
    have allpos : ∀ d, 0 < x .aux2 d := by
      intro d
      have := all (b - d).val
      rwa [Fin.cast_val_eq_self, sub_sub_cancel] at this
    have allU : ∀ d, U3 x d = v3 := by
      intro d
      have hzd : x .aux3 d = v2 := by
        have := (mul_eq_zero.1 (sp2 d)).resolve_left (allpos d).ne'
        linarith
      have := (mul_eq_zero.1 (sp3 d)).resolve_left (by rw [hzd]; exact hv2pos.ne')
      linarith
    have : ∑ d, U3 x d = (m + 1) * v3 := by rw [Finset.sum_congr rfl fun d _ => allU d, hcard]
    rw [hS] at this
    have hm : (0 : ℝ) < m + 1 := by positivity
    nlinarith
  have hU0 : ∀ d, U3 x d = 0 := by
    have hnp : ∀ d ∈ (Finset.univ : Finset (Fin (m + 1))), U3 x d ≤ 0 := fun d _ => hv3 ▸ br3 d
    intro d
    exact (Finset.sum_eq_zero_iff_of_nonpos hnp).1 hS d (Finset.mem_univ d)
  -- geometric shape
  have geo : ∀ n : ℕ, ∀ j : Fin (m + 1), (j : ℕ) + n = m →
      x .aux2 j = x .primary 0 ^ n * x .aux2 (Fin.last m) := by
    intro n
    induction n with
    | zero =>
      intro j hj
      have : j = Fin.last m := Fin.ext (by simpa using hj)
      simp [this]
    | succ n ih =>
      intro j hj
      have hlt : j < Fin.last m := by
        rw [Fin.lt_def, Fin.val_last]; omega
      have hv := Fin.val_add_one_of_lt hlt
      have hd0 : j + 1 ≠ 0 := by
        intro h0
        have := congrArg Fin.val h0
        rw [hv] at this
        simp at this
      have hu := hU0 (j + 1)
      unfold U3 at hu
      rw [add_sub_cancel_right, if_neg hd0, mul_zero, sub_zero] at hu
      rw [ih (j + 1) (by rw [hv]; omega)] at hu
      rw [pow_succ]
      linarith
  have hgeo : ∀ j : Fin (m + 1), x .aux2 j = x .primary 0 ^ (m - (j : ℕ)) * x .aux2 (Fin.last m) :=
    fun j => geo _ j (by have := j.isLt; omega)
  have hlast : 0 < x .aux2 (Fin.last m) := by
    rcases (hY.1 (Fin.last m)).lt_or_eq with h | h
    · exact h
    · exfalso
      have : ∑ b, x .aux2 b = 0 := by
        rw [Finset.sum_congr rfl fun j _ => hgeo j]
        simp [← h]
      rw [hy] at this; norm_num at this
  have hF : ∑ b, x .aux2 b * c b = x .aux2 (Fin.last m) * poly c (x .primary 0) := by
    unfold poly
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hgeo j]; ring
  have b0 := br1 0
  have b1 := br1 1
  simp only [U1, Fin.sum_univ_two, show (0 : Fin 2) ≠ 1 by decide, if_false, if_true,
    mul_zero, zero_add] at b0 b1
  rw [hF] at b0 b1
  refine ⟨hgeo, hlast, ?_, ?_, ?_⟩
  · have : 0 ≤ x .aux2 (Fin.last m) * (x .primary 1 * poly c (x .primary 0)) := by linarith
    exact (mul_nonneg_iff_of_pos_left hlast).1 this
  · have e : x .aux2 (Fin.last m) * (- (x .primary 0 * poly c (x .primary 0))) =
        x .primary 1 * (x .aux2 (Fin.last m) * poly c (x .primary 0)) -
          x .aux2 (Fin.last m) * poly c (x .primary 0) := by
      linear_combination (-(x .aux2 (Fin.last m) * poly c (x .primary 0))) * hp
    have : 0 ≤ x .aux2 (Fin.last m) * (- (x .primary 0 * poly c (x .primary 0))) := by
      rw [e]; linarith
    have := (mul_nonneg_iff_of_pos_left hlast).1 this
    linarith
  · intro b hb
    have := (mul_eq_zero.1 (sp2 b)).resolve_left hb.ne'
    linarith

lemma part1 {m : ℕ} (c : Fin (m + 1) → ℝ)
    (hf0 : poly c 0 ≤ 0) (hf1 : 0 ≤ poly c 1) (α : ℝ)
    (hα : 0 ≤ α ∧ α ≤ 1 ∧ poly c α = 0 ∧
      ∀ β : ℝ, 0 ≤ β → β ≤ 1 → poly c β = 0 → β = α)
    (x : ∀ p, Strat m p → ℝ) (hx : AGT.IsMixedNash (gadget c) x) :
    x .primary 0 = α ∧ x .primary 1 = 1 - α := by
  obtain ⟨-, -, hA, hB, -⟩ := ne_struct c x hx
  have hP := hx.1 .primary
  have hp : x .primary 0 + x .primary 1 = 1 := by
    have := hP.2; rwa [Fin.sum_univ_two] at this
  have hp0 : 0 ≤ x .primary 0 := hP.1 0
  have hp1 : 0 ≤ x .primary 1 := hP.1 1
  have hle : x .primary 0 ≤ 1 := by linarith
  have hroot : poly c (x .primary 0) = 0 := by
    rcases hp0.lt_or_eq with h0 | h0
    · rcases hle.lt_or_eq with h1 | h1
      · have hp1' : 0 < x .primary 1 := by linarith
        have a := (mul_nonneg_iff_of_pos_left hp1').1 hA
        have b : x .primary 0 * poly c (x .primary 0) ≤ 0 := hB
        have b' : poly c (x .primary 0) ≤ 0 := by
          by_contra hc; have hc' := not_le.1 hc; nlinarith
        linarith
      · rw [h1] at hB ⊢
        linarith
    · rw [← h0] at hA ⊢
      have : x .primary 1 = 1 := by rw [← h0] at hp; linarith
      rw [this] at hA
      linarith
  have := hα.2.2.2 _ hp0 hle hroot
  exact ⟨this, by linarith⟩

/-- the normalising sum -/
noncomputable def S {m : ℕ} (α : ℝ) : ℝ := ∑ i : Fin (m + 1), α ^ (m - (i : ℕ))

lemma S_pos {m : ℕ} (α : ℝ) (h : 0 ≤ α) : 0 < S (m := m) α := by
  unfold S
  have h1 : α ^ (m - ((Fin.last m : Fin (m + 1)) : ℕ)) ≤ ∑ i : Fin (m + 1), α ^ (m - (i : ℕ)) :=
    Finset.single_le_sum (f := fun i : Fin (m + 1) => α ^ (m - (i : ℕ)))
      (fun i _ => pow_nonneg h _) (Finset.mem_univ _)
  simp only [Fin.val_last, Nat.sub_self, pow_zero] at h1
  linarith

/-- the explicit equilibrium -/
noncomputable def xstar {m : ℕ} (α : ℝ) : ∀ p, Strat m p → ℝ
  | .primary => fun (s : Fin 2) => if s = 0 then α else 1 - α
  | .aux2 => fun (j : Fin (m + 1)) => α ^ (m - (j : ℕ)) / S (m := m) α
  | .aux3 => fun _ => 1 / ((m : ℝ) + 1)

lemma xs0 {m : ℕ} (α : ℝ) : xstar (m := m) α .primary 0 = α := rfl
lemma xs1 {m : ℕ} (α : ℝ) : xstar (m := m) α .primary 1 = 1 - α := rfl
lemma xs2 {m : ℕ} (α : ℝ) (j : Fin (m + 1)) :
    xstar (m := m) α .aux2 j = α ^ (m - (j : ℕ)) / S (m := m) α := rfl
lemma xs3 {m : ℕ} (α : ℝ) (j : Fin (m + 1)) : xstar (m := m) α .aux3 j = 1 / ((m : ℝ) + 1) := rfl

lemma fin2_cases (s : Fin 2) : s = 0 ∨ s = 1 := by
  rcases s with ⟨k, hk⟩
  interval_cases k <;> simp

lemma xstar_ne {m : ℕ} (c : Fin (m + 1) → ℝ) (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1)
    (hf : poly c α = 0) : AGT.IsMixedNash (gadget c) (xstar (m := m) α) := by
  have hS := S_pos (m := m) α h0
  have hm : (0 : ℝ) < m + 1 := by positivity
  have hp : xstar (m := m) α .primary 0 + xstar (m := m) α .primary 1 = 1 := by
    rw [xs0, xs1]; ring
  have hy : ∑ b, xstar (m := m) α .aux2 b = 1 := by
    simp only [xs2]
    rw [← Finset.sum_div]
    exact div_self hS.ne'
  have hz : ∑ b, xstar (m := m) α .aux3 b = 1 := by
    simp only [xs3, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  have hU3 : ∀ d, U3 (xstar (m := m) α) d = 0 := by
    have hne : ∀ d : Fin (m + 1), d ≠ 0 → U3 (xstar (m := m) α) d = 0 := by
      intro d hd
      unfold U3
      rw [if_neg hd, mul_zero, sub_zero, xs0, xs2, xs2, Fin.val_sub_one_of_ne_zero hd]
      have hd1 : 1 ≤ (d : ℕ) := Nat.one_le_iff_ne_zero.2 (fun h => hd (Fin.ext h))
      have hdm : (d : ℕ) ≤ m := Nat.lt_succ_iff.1 d.isLt
      rw [show m - ((d : ℕ) - 1) = (m - (d : ℕ)) + 1 by omega, pow_succ]
      ring
    have hsum := sumU3 (xstar (m := m) α) hp hy
    rw [Fin.sum_univ_succ, Finset.sum_eq_zero (fun i _ => hne _ (Fin.succ_ne_zero i)),
      add_zero] at hsum
    intro d
    by_cases hd : d = 0
    · rw [hd]; exact hsum
    · exact hne d hd
  have hprof : AGT.IsMixedProfile (xstar (m := m) α) := by
    intro i
    cases i
    · refine ⟨fun s => ?_, ?_⟩
      · rcases fin2_cases s with rfl | rfl
        · exact h0
        · show 0 ≤ 1 - α; linarith
      · show ∑ s : Fin 2, xstar (m := m) α .primary s = 1
        rw [Fin.sum_univ_two]; exact hp
    · refine ⟨fun s => ?_, hy⟩
      show 0 ≤ α ^ (m - ((s : Fin (m + 1)) : ℕ)) / S (m := m) α
      exact div_nonneg (pow_nonneg h0 _) hS.le
    · refine ⟨fun s => ?_, hz⟩
      show 0 ≤ 1 / ((m : ℝ) + 1)
      positivity
  refine ⟨hprof, ?_⟩
  intro i τ hτ
  cases i
  · rw [E1 c _ hz τ]
    have e := E1 c (xstar (m := m) α) hz (xstar (m := m) α .primary)
    rw [Function.update_eq_self] at e
    rw [e]
    have hU : ∀ t, U1 c (xstar (m := m) α) t = 0 := by
      intro t
      unfold U1
      split_ifs
      · simp only [xs2]
        have : ∑ b : Fin (m + 1), α ^ (m - (b : ℕ)) / S (m := m) α * c b
            = poly c α / S (m := m) α := by
          unfold poly
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
        rw [this, hf, zero_div]
      · rfl
    rw [const_sum _ _ 0 hU hτ, const_sum _ _ 0 hU (hprof .primary)]
  · rw [E2 c _ hp τ]
    have e := E2 c (xstar (m := m) α) hp (xstar (m := m) α .aux2)
    rw [Function.update_eq_self] at e
    rw [e, const_sum _ _ _ (xs3 α) hτ, const_sum _ _ _ (xs3 α) (hprof .aux2)]
  · rw [E3 c _ hp hy τ]
    have e := E3 c (xstar (m := m) α) hp hy (xstar (m := m) α .aux3)
    rw [Function.update_eq_self] at e
    rw [e, const_sum _ _ 0 hU3 hτ, const_sum _ _ 0 hU3 (hprof .aux3)]

lemma ne_eq_xstar {m : ℕ} (c : Fin (m + 1) → ℝ)
    (hf0 : poly c 0 ≤ 0) (hf1 : 0 ≤ poly c 1) (α : ℝ)
    (hα : 0 ≤ α ∧ α ≤ 1 ∧ poly c α = 0 ∧
      ∀ β : ℝ, 0 ≤ β → β ≤ 1 → poly c β = 0 → β = α)
    (ha0 : α ≠ 0) (x : ∀ p, Strat m p → ℝ) (hx : AGT.IsMixedNash (gadget c) x) :
    x = xstar (m := m) α := by
  obtain ⟨hp0, hp1⟩ := part1 c hf0 hf1 α hα x hx
  obtain ⟨hgeo, hlast, -, -, hzb⟩ := ne_struct c x hx
  have hapos : 0 < α := lt_of_le_of_ne hα.1 (Ne.symm ha0)
  have hS := S_pos (m := m) α hα.1
  have hy : ∑ b, x .aux2 b = 1 := (hx.1 .aux2).2
  have hz : ∑ b, x .aux3 b = 1 := (hx.1 .aux3).2
  rw [hp0] at hgeo
  have hyl : x .aux2 (Fin.last m) * S (m := m) α = 1 := by
    rw [← hy, Finset.sum_congr rfl fun j _ => hgeo j]
    unfold S
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hy' : ∀ j : Fin (m + 1), x .aux2 j = α ^ (m - (j : ℕ)) / S (m := m) α := by
    intro j
    rw [hgeo j, eq_div_iff hS.ne', mul_assoc, hyl, mul_one]
  have hz' : ∀ b : Fin (m + 1), x .aux3 b = 1 / ((m : ℝ) + 1) := by
    have hall : ∀ b : Fin (m + 1), x .aux3 b = ∑ s, x .aux2 s * x .aux3 s := fun b =>
      hzb b (by rw [hy' b]; exact div_pos (pow_pos hapos _) hS)
    have hsum : ∑ b : Fin (m + 1), x .aux3 b = ((m : ℝ) + 1) * ∑ s, x .aux2 s * x .aux3 s := by
      rw [Finset.sum_congr rfl fun b _ => hall b]
      simp
    rw [hz] at hsum
    intro b
    rw [hall b]
    have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    linarith
  funext p
  cases p
  · funext s
    rcases fin2_cases s with rfl | rfl
    · rw [hp0]; rfl
    · rw [hp1]; rfl
  · funext s
    exact hy' s
  · funext s
    exact hz' s

lemma xstar_full {m : ℕ} (α : ℝ) (h0 : 0 < α) (h1 : α < 1) :
    IsFullyMixed (xstar (m := m) α) := by
  intro p s
  cases p
  · rcases fin2_cases s with rfl | rfl
    · exact h0
    · show 0 < 1 - α; linarith
  · show 0 < α ^ (m - ((s : Fin (m + 1)) : ℕ)) / S (m := m) α
    exact div_pos (pow_pos h0 _) (S_pos α h0.le)
  · show 0 < 1 / ((m : ℝ) + 1)
    positivity

end FixpNash.Bubelis.L7Aux

open FixpNash.Bubelis in
theorem solution {m : ℕ} (c : Fin (m + 1) → ℝ)
    (hf0 : poly c 0 ≤ 0) (hf1 : 0 ≤ poly c 1) (α : ℝ)
    (hα : 0 ≤ α ∧ α ≤ 1 ∧ poly c α = 0 ∧
      ∀ β : ℝ, 0 ≤ β → β ≤ 1 → poly c β = 0 → β = α) :
    (∀ x : ∀ p, Strat m p → ℝ, AGT.IsMixedNash (gadget c) x →
        x .primary 0 = α ∧ x .primary 1 = 1 - α) ∧
      (α ≠ 0 → α ≠ 1 →
        (∃! x : ∀ p, Strat m p → ℝ, AGT.IsMixedNash (gadget c) x) ∧
          ∀ x : ∀ p, Strat m p → ℝ, AGT.IsMixedNash (gadget c) x → IsFullyMixed x) := by
  refine ⟨fun x hx => L7Aux.part1 c hf0 hf1 α hα x hx, fun h0 h1 => ⟨?_, ?_⟩⟩
  · exact ⟨L7Aux.xstar α, L7Aux.xstar_ne c α hα.1 hα.2.1 hα.2.2.1,
      fun y hy => L7Aux.ne_eq_xstar c hf0 hf1 α hα h0 y hy⟩
  · intro x hx
    rw [L7Aux.ne_eq_xstar c hf0 hf1 α hα h0 x hx]
    exact L7Aux.xstar_full α (lt_of_le_of_ne hα.1 (Ne.symm h0)) (lt_of_le_of_ne hα.2.1 h1)
