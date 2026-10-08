-- Prove2me | solution 1 for DiscreteConvex.EconomicEquilibriumB.equilibrium_price_set_is_lnat_polyhedron
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T23:45:01.658714+00:00
-- url     : https://prove2.me/submissions/b26365a3-7a7b-4400-a0d9-fb6d44a37a1c

import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_IsLNaturalConvexPolyhedron
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_EquilibriumPriceSet
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_EquilibriumPricePolyhedronE
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_MNaturalConcave
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_MNaturalConvexC
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_IsOptimalAllocation



namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]

example (a b : ℤ) : (a - b).natAbs ≤ (a + 1 - b).natAbs ∨ a < b := by omega

lemma eqb_bot_contra (a b c d : WithBot ℝ) (ha : a ≠ ⊥) (hab : a < b) (hc : c ≤ a) (hd : d ≤ a)
    (h : b + a ≤ c + d) : False := by
  induction a using WithBot.recBotCoe with
  | bot => exact ha rfl
  | coe r =>
  induction b using WithBot.recBotCoe with
  | bot => exact absurd hab (by simp)
  | coe s =>
  induction c using WithBot.recBotCoe with
  | bot => simp at h
  | coe u =>
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe v =>
  norm_cast at hab hc hd h
  linarith

lemma eqb_top_contra (a b c d : WithTop ℝ) (ha : a ≠ ⊤) (hab : b < a) (hc : a ≤ c) (hd : a ≤ d)
    (h : c + d ≤ b + a) : False := by
  induction a using WithTop.recTopCoe with
  | top => exact ha rfl
  | coe r =>
  induction b using WithTop.recTopCoe with
  | top => exact absurd hab (by simp)
  | coe s =>
  induction c using WithTop.recTopCoe with
  | top => simp at h
  | coe u =>
  induction d using WithTop.recTopCoe with
  | top => simp at h
  | coe v =>
  norm_cast at hab hc hd h
  linarith

lemma eqb_ps_add (U : (K → ℤ) → WithBot ℝ) (p : K → ℝ) (a b c d : K → ℤ)
    (hs : ∀ w, a w + b w = c w + d w) (h : U a + U b ≤ U c + U d) :
    PriceShift U p a + PriceShift U p b ≤ PriceShift U p c + PriceShift U p d := by
  have hlin : (-(∑ k, p k * (a k : ℝ))) + (-(∑ k, p k * (b k : ℝ))) =
      (-(∑ k, p k * (c k : ℝ))) + (-(∑ k, p k * (d k : ℝ))) := by
    have : ∀ k, p k * (a k : ℝ) + p k * (b k : ℝ) = p k * (c k : ℝ) + p k * (d k : ℝ) := by
      intro k; rw [← mul_add, ← mul_add]; congr 1; exact_mod_cast hs k
    have h2 := Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => this k)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at h2
    linarith
  unfold PriceShift
  rw [add_add_add_comm, add_add_add_comm (U c), ← WithBot.coe_add, ← WithBot.coe_add, hlin]
  exact add_le_add h le_rfl

lemma eqb_psc_add (C : (K → ℤ) → WithTop ℝ) (p : K → ℝ) (a b c d : K → ℤ)
    (hs : ∀ w, a w + b w = c w + d w) (h : C c + C d ≤ C a + C b) :
    PriceShiftConvex C p c + PriceShiftConvex C p d ≤ PriceShiftConvex C p a + PriceShiftConvex C p b := by
  have hlin : (-(∑ k, p k * (a k : ℝ))) + (-(∑ k, p k * (b k : ℝ))) =
      (-(∑ k, p k * (c k : ℝ))) + (-(∑ k, p k * (d k : ℝ))) := by
    have : ∀ k, p k * (a k : ℝ) + p k * (b k : ℝ) = p k * (c k : ℝ) + p k * (d k : ℝ) := by
      intro k; rw [← mul_add, ← mul_add]; congr 1; exact_mod_cast hs k
    have h2 := Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => this k)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at h2
    linarith
  unfold PriceShiftConvex
  rw [add_add_add_comm, add_add_add_comm (C a), ← WithTop.coe_add, ← WithTop.coe_add, hlin]
  exact add_le_add h le_rfl


def eqbD (x y : K → ℤ) : ℕ := ∑ k, (y k - x k).natAbs

lemma eqbD_dec1 (x y : K → ℤ) (i : K) (hi : x i < y i) :
    eqbD x (fun w => y w - (if w = i then (1:ℤ) else 0)) < eqbD x y := by
  unfold eqbD
  apply Finset.sum_lt_sum
  · intro k _; by_cases h : k = i <;> simp [h] <;> omega
  · exact ⟨i, Finset.mem_univ _, by simp; omega⟩

lemma eqbD_dec2 (x y : K → ℤ) (i : K) (hi : y i < x i) :
    eqbD x (fun w => y w + (if w = i then (1:ℤ) else 0)) < eqbD x y := by
  unfold eqbD
  apply Finset.sum_lt_sum
  · intro k _; by_cases h : k = i <;> simp [h] <;> omega
  · exact ⟨i, Finset.mem_univ _, by simp; omega⟩

lemma eqbD_dec3 (x y : K → ℤ) (i j : K) (hi : x i < y i) (hj : y j < x j) :
    eqbD x (fun w => y w - (if w = i then (1:ℤ) else 0) + (if w = j then (1:ℤ) else 0)) < eqbD x y := by
  have hij : i ≠ j := by rintro rfl; omega
  unfold eqbD
  apply Finset.sum_lt_sum
  · intro k _
    by_cases h : k = i
    · subst h; simp [hij]; omega
    · by_cases h' : k = j
      · subst h'; simp [h]; omega
      · simp [h, h']
  · exact ⟨i, Finset.mem_univ _, by simp [hij]; omega⟩

lemma eqb_local_global_U (U : (K → ℤ) → WithBot ℝ) (hU : MNaturalConcave U) (p : K → ℝ)
    (x : K → ℤ) (hx : U x ≠ ⊥)
    (h1 : ∀ j, PriceShift U p (fun k => x k + if k = j then (1:ℤ) else 0) ≤ PriceShift U p x)
    (h2 : ∀ j, PriceShift U p (fun k => x k - if k = j then (1:ℤ) else 0) ≤ PriceShift U p x)
    (h3 : ∀ i j, i ≠ j → PriceShift U p (fun k => x k + (if k = i then (1:ℤ) else 0) -
      (if k = j then (1:ℤ) else 0)) ≤ PriceShift U p x) :
    x ∈ ArgMaxBot (PriceShift U p) := by
  have hgx : PriceShift U p x ≠ ⊥ := by
    unfold PriceShift; intro h; rw [WithBot.add_eq_bot] at h; simp_all
  suffices H : ∀ n, ∀ y, eqbD x y = n → PriceShift U p y ≤ PriceShift U p x by
    intro y; exact H _ y rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro y hyn
  have IH : ∀ y', eqbD x y' < eqbD x y → PriceShift U p y' ≤ PriceShift U p x :=
    fun y' hy' => ih _ (hyn ▸ hy') y' rfl
  by_contra hlt
  rw [not_le] at hlt
  have hy : U y ≠ ⊥ := by
    intro h; unfold PriceShift at hlt; rw [h] at hlt; simp at hlt
  by_cases hA : ∃ i, x i < y i
  · obtain ⟨i, hi⟩ := hA
    have hiS : i ∈ SuppPos y x := by simp [SuppPos, hi]
    have hex := hU.2 y hy x hx i hiS
    rcases le_max_iff.1 hex with h | h
    · have := eqb_ps_add U p y x _ _ (by intro w; ring) h
      exact eqb_bot_contra _ _ _ _ hgx hlt (IH _ (eqbD_dec1 x y i hi)) (h1 i)
        (by simpa using this)
    · by_cases hne : (SuppNeg y x).Nonempty
      · obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_sup _ hne (fun j =>
          U (fun w => y w - (if w = i then (1:ℤ) else 0) + (if w = j then (1:ℤ) else 0)) +
            U (fun w => x w + (if w = i then (1:ℤ) else 0) - (if w = j then (1:ℤ) else 0)))
        rw [hjeq] at h
        have hj' : y j < x j := by simpa [SuppNeg] using hj
        have hij : i ≠ j := by rintro rfl; omega
        have := eqb_ps_add U p y x _ _ (by intro w; ring) h
        exact eqb_bot_contra _ _ _ _ hgx hlt (IH _ (eqbD_dec3 x y i j hi hj')) (h3 i j hij)
          this
      · rw [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.sup_empty] at h
        rw [le_bot_iff, WithBot.add_eq_bot] at h
        tauto
  · push_neg at hA
    have hne : ∃ i, y i < x i := by
      by_contra hc
      push_neg at hc
      have : y = x := funext fun k => le_antisymm (hA k) (hc k)
      rw [this] at hlt; exact lt_irrefl _ hlt
    obtain ⟨i, hi⟩ := hne
    have hiS : i ∈ SuppPos x y := by simp [SuppPos, hi]
    have hex := hU.2 x hx y hy i hiS
    have hemp : SuppNeg x y = ∅ := by
      ext k; simp [SuppNeg]; exact hA k
    rw [hemp, Finset.sup_empty] at hex
    rw [max_eq_left bot_le] at hex
    have := eqb_ps_add U p x y _ _ (by intro w; ring) hex
    rw [add_comm (PriceShift U p x)] at this
    exact eqb_bot_contra _ _ _ _ hgx hlt (h2 i) (IH _ (eqbD_dec2 x y i hi)) this


lemma eqb_local_global_C (C : (K → ℤ) → WithTop ℝ) (hC : MNaturalConvexC C) (p : K → ℝ)
    (x : K → ℤ) (hx : C x ≠ ⊤)
    (h1 : ∀ j, PriceShiftConvex C p x ≤ PriceShiftConvex C p (fun k => x k + if k = j then (1:ℤ) else 0))
    (h2 : ∀ j, PriceShiftConvex C p x ≤ PriceShiftConvex C p (fun k => x k - if k = j then (1:ℤ) else 0))
    (h3 : ∀ i j, i ≠ j → PriceShiftConvex C p x ≤ PriceShiftConvex C p
      (fun k => x k + (if k = i then (1:ℤ) else 0) - (if k = j then (1:ℤ) else 0))) :
    x ∈ ArgMinTop (PriceShiftConvex C p) := by
  have hgx : PriceShiftConvex C p x ≠ ⊤ := by
    unfold PriceShiftConvex; intro h; rw [WithTop.add_eq_top] at h
    rcases h with h | h
    · exact hx h
    · exact WithTop.coe_ne_top h
  suffices H : ∀ n, ∀ y, eqbD x y = n → PriceShiftConvex C p x ≤ PriceShiftConvex C p y by
    intro y; exact H _ y rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro y hyn
  have IH : ∀ y', eqbD x y' < eqbD x y → PriceShiftConvex C p x ≤ PriceShiftConvex C p y' :=
    fun y' hy' => ih _ (hyn ▸ hy') y' rfl
  by_contra hlt
  rw [not_le] at hlt
  have hy : C y ≠ ⊤ := by
    intro h; unfold PriceShiftConvex at hlt; rw [h] at hlt; simp at hlt
  by_cases hA : ∃ i, x i < y i
  · obtain ⟨i, hi⟩ := hA
    have hiS : i ∈ SuppPos y x := by simp [SuppPos, hi]
    have hex := hC.2 y hy x hx i hiS
    rcases min_le_iff.1 hex with h | h
    · have := eqb_psc_add C p y x _ _ (by intro w; ring) h
      exact eqb_top_contra _ _ _ _ hgx hlt (IH _ (eqbD_dec1 x y i hi)) (h1 i)
        (by simpa using this)
    · by_cases hne : (SuppNeg y x).Nonempty
      · obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_inf _ hne (fun j =>
          C (fun w => y w - (if w = i then (1:ℤ) else 0) + (if w = j then (1:ℤ) else 0)) +
            C (fun w => x w + (if w = i then (1:ℤ) else 0) - (if w = j then (1:ℤ) else 0)))
        rw [hjeq] at h
        have hj' : y j < x j := by simpa [SuppNeg] using hj
        have hij : i ≠ j := by rintro rfl; omega
        have := eqb_psc_add C p y x _ _ (by intro w; ring) h
        exact eqb_top_contra _ _ _ _ hgx hlt (IH _ (eqbD_dec3 x y i j hi hj')) (h3 i j hij)
          this
      · rw [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.inf_empty] at h
        rw [top_le_iff, WithTop.add_eq_top] at h
        tauto
  · push_neg at hA
    have hne : ∃ i, y i < x i := by
      by_contra hc
      push_neg at hc
      have : y = x := funext fun k => le_antisymm (hA k) (hc k)
      rw [this] at hlt; exact lt_irrefl _ hlt
    obtain ⟨i, hi⟩ := hne
    have hiS : i ∈ SuppPos x y := by simp [SuppPos, hi]
    have hex := hC.2 x hx y hy i hiS
    have hemp : SuppNeg x y = ∅ := by
      ext k; simp [SuppNeg]; exact hA k
    rw [hemp, Finset.inf_empty] at hex
    rw [min_eq_left le_top] at hex
    have := eqb_psc_add C p x y _ _ (by intro w; ring) hex
    rw [add_comm (PriceShiftConvex C p x)] at this
    exact eqb_top_contra _ _ _ _ hgx hlt (h2 i) (IH _ (eqbD_dec2 x y i hi)) this


lemma eqb_ps_le_iff (U : (K → ℤ) → WithBot ℝ) (p : K → ℝ) (x z : K → ℤ) (b : ℝ) (hb : U x = ↑b)
    (δ : ℝ) (hd : ∑ k, p k * (z k : ℝ) = ∑ k, p k * (x k : ℝ) + δ) :
    PriceShift U p z ≤ PriceShift U p x ↔ U z ≤ ↑(b + δ) := by
  unfold PriceShift
  rw [hb, hd]
  induction U z using WithBot.recBotCoe with
  | bot => simp
  | coe r =>
    rw [← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_le_coe, WithBot.coe_le_coe]
    constructor <;> intro h <;> linarith

lemma eqb_psc_le_iff (C : (K → ℤ) → WithTop ℝ) (p : K → ℝ) (x z : K → ℤ) (b : ℝ) (hb : C x = ↑b)
    (δ : ℝ) (hd : ∑ k, p k * (z k : ℝ) = ∑ k, p k * (x k : ℝ) + δ) :
    PriceShiftConvex C p x ≤ PriceShiftConvex C p z ↔ ↑(b + δ) ≤ C z := by
  unfold PriceShiftConvex
  rw [hb, hd]
  induction C z using WithTop.recTopCoe with
  | top => simp
  | coe r =>
    rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe, WithTop.coe_le_coe]
    constructor <;> intro h <;> linarith

@[simp] lemma eqb_tb_bot : ToERealOfBot (⊥ : WithBot ℝ) = ⊥ := rfl
@[simp] lemma eqb_tb_coe (r : ℝ) : ToERealOfBot ((r : ℝ) : WithBot ℝ) = (r : EReal) := rfl
@[simp] lemma eqb_tt_top : ToEReal (⊤ : WithTop ℝ) = ⊤ := rfl
@[simp] lemma eqb_tt_coe (r : ℝ) : ToEReal ((r : ℝ) : WithTop ℝ) = (r : EReal) := rfl

lemma eqb_E1 (u : WithBot ℝ) (b t : ℝ) :
    ToERealOfBot u - ToERealOfBot (↑b) ≤ ((t : ℝ) : EReal) ↔ u ≤ ↑(b + t) := by
  induction u using WithBot.recBotCoe with
  | bot => simp
  | coe r =>
    simp only [eqb_tb_coe]
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff, WithBot.coe_le_coe]
    constructor <;> intro h <;> linarith

lemma eqb_E2 (u : WithBot ℝ) (b t : ℝ) :
    ((t : ℝ) : EReal) ≤ ToERealOfBot (↑b) - ToERealOfBot u ↔ u ≤ ↑(b - t) := by
  induction u using WithBot.recBotCoe with
  | bot => simp
  | coe r =>
    simp only [eqb_tb_coe]
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff, WithBot.coe_le_coe]
    constructor <;> intro h <;> linarith

lemma eqb_E3 (c : WithTop ℝ) (b t : ℝ) :
    ToEReal (↑b) - ToEReal c ≤ ((t : ℝ) : EReal) ↔ ((b - t : ℝ) : WithTop ℝ) ≤ c := by
  induction c using WithTop.recTopCoe with
  | top => simp
  | coe r =>
    simp only [eqb_tt_coe]
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff, WithTop.coe_le_coe]
    constructor <;> intro h <;> linarith

lemma eqb_E4 (c : WithTop ℝ) (b t : ℝ) :
    ((t : ℝ) : EReal) ≤ ToEReal c - ToEReal (↑b) ↔ ((b + t : ℝ) : WithTop ℝ) ≤ c := by
  induction c using WithTop.recTopCoe with
  | top => simp
  | coe r =>
    simp only [eqb_tt_coe]
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff, WithTop.coe_le_coe]
    constructor <;> intro h <;> linarith

lemma eqb_lin1 (p : K → ℝ) (x : K → ℤ) (j : K) :
    ∑ k, p k * (((x k + if k = j then (1:ℤ) else 0 : ℤ)) : ℝ) = ∑ k, p k * (x k : ℝ) + p j := by
  push_cast; simp [mul_add, Finset.sum_add_distrib]

lemma eqb_lin2 (p : K → ℝ) (x : K → ℤ) (j : K) :
    ∑ k, p k * (((x k - if k = j then (1:ℤ) else 0 : ℤ)) : ℝ) = ∑ k, p k * (x k : ℝ) + -p j := by
  push_cast; simp [mul_sub, Finset.sum_sub_distrib]; ring

lemma eqb_lin3 (p : K → ℝ) (x : K → ℤ) (i j : K) :
    ∑ k, p k * (((x k + (if k = i then (1:ℤ) else 0) - (if k = j then (1:ℤ) else 0) : ℤ)) : ℝ) =
      ∑ k, p k * (x k : ℝ) + (p i - p j) := by
  push_cast; simp [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]; ring


lemma eqb_demand_iff (U : (K → ℤ) → WithBot ℝ) (hU : MNaturalConcave U) (p : K → ℝ)
    (x : K → ℤ) (hx : U x ≠ ⊥) :
    x ∈ DemandSet U p ↔
      ((∀ j, ToERealOfBot (U (fun k => x k + if k = j then (1:ℤ) else 0)) - ToERealOfBot (U x)
          ≤ ((p j : ℝ) : EReal)) ∧
      (∀ j, ((p j : ℝ) : EReal) ≤
          ToERealOfBot (U x) - ToERealOfBot (U (fun k => x k - if k = j then (1:ℤ) else 0))) ∧
      (∀ i j, i ≠ j → ((p j - p i : ℝ) : EReal) ≤ ToERealOfBot (U x) -
          ToERealOfBot (U (fun k => x k + (if k = i then (1:ℤ) else 0) -
            (if k = j then (1:ℤ) else 0))))) := by
  obtain ⟨b, hb⟩ := WithBot.ne_bot_iff_exists.1 hx
  have hb' := hb.symm
  have c1 : ∀ j, (ToERealOfBot (U (fun k => x k + if k = j then (1:ℤ) else 0)) -
      ToERealOfBot (U x) ≤ ((p j : ℝ) : EReal)) ↔
      PriceShift U p (fun k => x k + if k = j then (1:ℤ) else 0) ≤ PriceShift U p x := by
    intro j
    rw [eqb_ps_le_iff U p x _ b hb' (p j) (eqb_lin1 p x j), hb', eqb_E1]
  have c2 : ∀ j, (((p j : ℝ) : EReal) ≤
      ToERealOfBot (U x) - ToERealOfBot (U (fun k => x k - if k = j then (1:ℤ) else 0))) ↔
      PriceShift U p (fun k => x k - if k = j then (1:ℤ) else 0) ≤ PriceShift U p x := by
    intro j
    rw [eqb_ps_le_iff U p x _ b hb' (-p j) (eqb_lin2 p x j), hb', eqb_E2, ← sub_eq_add_neg]
  have c3 : ∀ i j, (((p j - p i : ℝ) : EReal) ≤ ToERealOfBot (U x) -
      ToERealOfBot (U (fun k => x k + (if k = i then (1:ℤ) else 0) -
        (if k = j then (1:ℤ) else 0)))) ↔
      PriceShift U p (fun k => x k + (if k = i then (1:ℤ) else 0) -
        (if k = j then (1:ℤ) else 0)) ≤ PriceShift U p x := by
    intro i j
    rw [eqb_ps_le_iff U p x _ b hb' (p i - p j) (eqb_lin3 p x i j), hb', eqb_E2]
    have : b - (p j - p i) = b + (p i - p j) := by ring
    rw [this]
  simp only [c1, c2, c3]
  constructor
  · intro h
    exact ⟨fun j => h _, fun j => h _, fun i j _ => h _⟩
  · rintro ⟨h1, h2, h3⟩
    exact eqb_local_global_U U hU p x hx h1 h2 h3

lemma eqb_supply_iff (C : (K → ℤ) → WithTop ℝ) (hC : MNaturalConvexC C) (p : K → ℝ)
    (y : K → ℤ) (hy : C y ≠ ⊤) :
    y ∈ SupplySet C p ↔
      ((∀ j, ToEReal (C y) - ToEReal (C (fun k => y k - if k = j then (1:ℤ) else 0))
          ≤ ((p j : ℝ) : EReal)) ∧
      (∀ j, ((p j : ℝ) : EReal) ≤
          ToEReal (C (fun k => y k + if k = j then (1:ℤ) else 0)) - ToEReal (C y)) ∧
      (∀ i j, i ≠ j → ((p j - p i : ℝ) : EReal) ≤
          ToEReal (C (fun k => y k - (if k = i then (1:ℤ) else 0) +
            (if k = j then (1:ℤ) else 0))) - ToEReal (C y))) := by
  obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.1 hy
  have hb' := hb.symm
  have c1 : ∀ j, (ToEReal (C y) - ToEReal (C (fun k => y k - if k = j then (1:ℤ) else 0))
          ≤ ((p j : ℝ) : EReal)) ↔
      PriceShiftConvex C p y ≤ PriceShiftConvex C p (fun k => y k - if k = j then (1:ℤ) else 0) := by
    intro j
    rw [eqb_psc_le_iff C p y _ b hb' (-p j) (eqb_lin2 p y j), hb', eqb_E3, ← sub_eq_add_neg]
  have c2 : ∀ j, (((p j : ℝ) : EReal) ≤
          ToEReal (C (fun k => y k + if k = j then (1:ℤ) else 0)) - ToEReal (C y)) ↔
      PriceShiftConvex C p y ≤ PriceShiftConvex C p (fun k => y k + if k = j then (1:ℤ) else 0) := by
    intro j
    rw [eqb_psc_le_iff C p y _ b hb' (p j) (eqb_lin1 p y j), hb', eqb_E4]
  have c3 : ∀ i j, (((p j - p i : ℝ) : EReal) ≤
          ToEReal (C (fun k => y k - (if k = i then (1:ℤ) else 0) +
            (if k = j then (1:ℤ) else 0))) - ToEReal (C y)) ↔
      PriceShiftConvex C p y ≤ PriceShiftConvex C p (fun k => y k + (if k = j then (1:ℤ) else 0) -
        (if k = i then (1:ℤ) else 0)) := by
    intro i j
    have hf : (fun k => y k - (if k = i then (1:ℤ) else 0) + (if k = j then (1:ℤ) else 0)) =
        (fun k => y k + (if k = j then (1:ℤ) else 0) - (if k = i then (1:ℤ) else 0)) :=
      funext fun k => by ring
    rw [hf, eqb_psc_le_iff C p y _ b hb' (p j - p i) (eqb_lin3 p y j i), hb', eqb_E4]
  simp only [c1, c2, c3]
  constructor
  · intro h
    exact ⟨fun j => h _, fun j => h _, fun i j _ => h _⟩
  · rintro ⟨h1, h2, h3⟩
    exact eqb_local_global_C C hC p y hy h2 h1 (fun i j hij => h3 j i (Ne.symm hij))


lemma eqb_lnat_generic (lo up : K → EReal) (c : K → K → EReal) :
    IsLNaturalConvexPolyhedron {p : K → ℝ | (∀ j, lo j ≤ ((p j : ℝ) : EReal) ∧
      ((p j : ℝ) : EReal) ≤ up j) ∧ ∀ i j, i ≠ j → ((p j - p i : ℝ) : EReal) ≤ c i j} := by
  have mono : ∀ (a b : ℝ) (X : EReal), a ≤ b → (b : EReal) ≤ X → (a : EReal) ≤ X :=
    fun a b X h h' => le_trans (EReal.coe_le_coe_iff.2 h) h'
  have mono' : ∀ (a b : ℝ) (X : EReal), a ≤ b → X ≤ (a : EReal) → X ≤ (b : EReal) :=
    fun a b X h h' => le_trans h' (EReal.coe_le_coe_iff.2 h)
  intro p ⟨hp1, hp2⟩ q ⟨hq1, hq2⟩ α hα
  refine ⟨⟨fun j => ⟨?_, ?_⟩, fun i j hij => ?_⟩, ⟨fun j => ⟨?_, ?_⟩, fun i j hij => ?_⟩⟩
  · beta_reduce; exact mono' _ _ _ (le_max_right _ _) (hq1 j).1
  · beta_reduce
    rcases le_total (p j - α) (q j) with h | h
    · rw [max_eq_right h]; exact (hq1 j).2
    · rw [max_eq_left h]; exact mono _ _ _ (by linarith) (hp1 j).2
  · beta_reduce
    rcases le_total (p j - α) (q j) with h | h
    · rw [max_eq_right h]
      exact mono _ _ _ (by linarith [le_max_right (p i - α) (q i)]) (hq2 i j hij)
    · rw [max_eq_left h]
      exact mono _ _ _ (by linarith [le_max_left (p i - α) (q i)]) (hp2 i j hij)
  · beta_reduce
    rcases le_total (p j) (q j + α) with h | h
    · rw [min_eq_left h]; exact (hp1 j).1
    · rw [min_eq_right h]; exact mono' _ _ _ (by linarith) (hq1 j).1
  · beta_reduce; exact mono _ _ _ (min_le_left _ _) (hp1 j).2
  · beta_reduce
    rcases le_total (p i) (q i + α) with h | h
    · rw [min_eq_left h]
      exact mono _ _ _ (by linarith [min_le_left (p j) (q j + α)]) (hp2 i j hij)
    · rw [min_eq_right h]
      exact mono _ _ _ (by linarith [min_le_right (p j) (q j + α)]) (hq2 i j hij)

theorem eqb_set_eq {H L : Type*} [Fintype H] [Fintype L]
    [Nonempty H] [Nonempty L] (U : H → (K → ℤ) → WithBot ℝ) (C : L → (K → ℤ) → WithTop ℝ)
    (x : H → (K → ℤ)) (y : L → (K → ℤ))
    (hU : ∀ h, MNaturalConcave (U h)) (hC : ∀ l, MNaturalConvexC (C l))
    (hopt : IsOptimalAllocation U C x y) :
    EquilibriumPriceSet U C x y = EquilibriumPricePolyhedronE U C x y := by
  ext p
  have hD := fun h => eqb_demand_iff (U h) (hU h) p (x h) (hopt.1 h)
  have hS := fun l => eqb_supply_iff (C l) (hC l) p (y l) (hopt.2.1 l)
  simp only [EquilibriumPriceSet, EquilibriumPricePolyhedronE, Set.mem_setOf_eq, hD, hS,
    LBoundJE, UBoundJE, UBoundIJE, max_le_iff, Finset.sup'_le_iff, le_min_iff,
    Finset.le_inf'_iff, Finset.mem_univ, true_implies]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun j => ⟨⟨?_, fun h => (h1 h).1 j, fun l => (h2 l).1 j⟩,
      fun h => (h1 h).2.1 j, fun l => (h2 l).2.1 j⟩,
      fun i j hij => ⟨fun h => (h1 h).2.2 i j hij, fun l => (h2 l).2.2 i j hij⟩⟩
    exact_mod_cast h3 j
  · rintro ⟨h1, h2⟩
    refine ⟨fun h => ⟨fun j => (h1 j).1.2.1 h, fun j => (h1 j).2.1 h,
      fun i j hij => (h2 i j hij).1 h⟩,
      fun l => ⟨fun j => (h1 j).1.2.2 l, fun j => (h1 j).2.2 l,
      fun i j hij => (h2 i j hij).2 l⟩, fun k => ?_⟩
    exact_mod_cast (h1 k).1.1

theorem eqb_goal_core {H L : Type*} [Fintype H] [Fintype L]
    [Nonempty H] [Nonempty L] (U : H → (K → ℤ) → WithBot ℝ) (C : L → (K → ℤ) → WithTop ℝ)
    (x : H → (K → ℤ)) (y : L → (K → ℤ))
    (hU : ∀ h, MNaturalConcave (U h)) (hC : ∀ l, MNaturalConvexC (C l))
    (hopt : IsOptimalAllocation U C x y) :
    IsLNaturalConvexPolyhedron (EquilibriumPriceSet U C x y) ∧
    EquilibriumPriceSet U C x y = EquilibriumPricePolyhedronE U C x y := by
  have he := eqb_set_eq U C x y hU hC hopt
  refine ⟨?_, he⟩
  rw [he]
  exact eqb_lnat_generic _ _ _

theorem eqb_exists_core {H L : Type*} [Fintype H] [Fintype L] [Nonempty H]
    [Nonempty L] (U : H → (K → ℤ) → WithBot ℝ) (C : L → (K → ℤ) → WithTop ℝ) (x : H → (K → ℤ))
    (y : L → (K → ℤ)) (hU : ∀ h, MNaturalConcave (U h)) (hC : ∀ l, MNaturalConvexC (C l))
    (hopt : IsOptimalAllocation U C x y) :
    (EquilibriumPriceSet U C x y).Nonempty ↔ (EquilibriumPricePolyhedronE U C x y).Nonempty := by
  rw [eqb_set_eq U C x y hU hC hopt]

end DiscreteConvex.EconomicEquilibriumB

open DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]

theorem solution {H L : Type*} [Fintype H] [Fintype L]
    [Nonempty H] [Nonempty L] (U : H → (K → ℤ) → WithBot ℝ) (C : L → (K → ℤ) → WithTop ℝ)
    (x : H → (K → ℤ)) (y : L → (K → ℤ))
    (hU : ∀ h, MNaturalConcave (U h)) (hC : ∀ l, MNaturalConvexC (C l))
    (hopt : IsOptimalAllocation U C x y) :
    IsLNaturalConvexPolyhedron (EquilibriumPriceSet U C x y) ∧
    EquilibriumPriceSet U C x y = EquilibriumPricePolyhedronE U C x y := by
  exact eqb_goal_core U C x y hU hC hopt
