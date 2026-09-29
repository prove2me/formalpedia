-- Prove2me | solution 1 for FrobeniusDensity.sum_moebius_mul_pos
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/b7a05384-0a38-501f-847a-0f605137f9bf

import Theorems.Thm_ArithmeticFunction_sum_moebius_filter_dvd
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Group
import Mathlib.Tactic.Positivity
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FrobeniusDensity_sum_moebius_mul_pos

set_option autoImplicit false

open Finset

namespace FrobeniusDensity

section Weight

variable {G : Type*} [Group G] [Finite G]

private theorem mem_zpowers_pow_div_iff (σ y : G) {f : ℕ} (hf : f ∣ orderOf σ) (hf0 : f ≠ 0) :
    y ∈ Subgroup.zpowers (σ ^ (orderOf σ / f))
      ↔ y ∈ Subgroup.zpowers σ ∧ orderOf y ∣ f := by
  have hn0 : orderOf σ ≠ 0 := (orderOf_pos σ).ne'
  constructor
  · intro hy
    obtain ⟨i, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hy)
    refine ⟨?_, ?_⟩
    · rw [← pow_mul]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers σ) _
    · rw [orderOf_dvd_iff_pow_eq_one, ← pow_mul, ← pow_mul]
      have h : orderOf σ / f * (i * f) = orderOf σ * i := by
        rw [show i * f = f * i from mul_comm i f, ← mul_assoc, Nat.div_mul_cancel hf]
      rw [h, pow_mul, pow_orderOf_eq_one, one_pow]
  · rintro ⟨hy, hyf⟩
    obtain ⟨j, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hy)
    have h1 : σ ^ (j * f) = 1 := by
      rw [pow_mul]
      exact orderOf_dvd_iff_pow_eq_one.mp hyf
    have h2 : orderOf σ ∣ j * f := orderOf_dvd_iff_pow_eq_one.mpr h1
    have h3 : orderOf σ / f ∣ j := by
      obtain ⟨c, hc⟩ := h2
      have hfpos : 0 < f := Nat.pos_of_ne_zero hf0
      refine ⟨c, Nat.eq_of_mul_eq_mul_right hfpos ?_⟩
      rw [mul_comm (orderOf σ / f) c, mul_assoc, Nat.div_mul_cancel hf, hc]
      ring
    obtain ⟨c, hc⟩ := h3
    rw [hc, pow_mul]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _

private theorem sum_moebius_mem_zpowers (σ y : G) :
    ∑ f ∈ (orderOf σ).divisors,
        (ArithmeticFunction.moebius (orderOf σ / f)) *
          (if y ∈ Subgroup.zpowers (σ ^ (orderOf σ / f)) then 1 else 0)
      = if y ∈ Subgroup.zpowers σ ∧ orderOf y = orderOf σ then 1 else 0 := by
  classical
  have hn0 : orderOf σ ≠ 0 := (orderOf_pos σ).ne'
  by_cases hy : y ∈ Subgroup.zpowers σ
  · have hdvd : orderOf y ∣ orderOf σ := orderOf_dvd_of_mem_zpowers hy
    have hcong : ∀ f ∈ (orderOf σ).divisors,
        (ArithmeticFunction.moebius (orderOf σ / f)) *
            (if y ∈ Subgroup.zpowers (σ ^ (orderOf σ / f)) then 1 else 0)
          = (ArithmeticFunction.moebius (orderOf σ / f)) *
              (if orderOf y ∣ f then 1 else 0) := by
      intro f hf
      obtain ⟨hfn, -⟩ := Nat.mem_divisors.mp hf
      have hf0 : f ≠ 0 := by
        rintro rfl
        exact hn0 (Nat.eq_zero_of_zero_dvd hfn)
      congr 1
      rw [if_congr (mem_zpowers_pow_div_iff σ y hfn hf0) rfl rfl]
      simp [hy]
    rw [Finset.sum_congr rfl hcong,
      ArithmeticFunction.sum_moebius_filter_dvd hn0 hdvd]
    simp [hy]
  · have hcong : ∀ f ∈ (orderOf σ).divisors,
        (ArithmeticFunction.moebius (orderOf σ / f)) *
            (if y ∈ Subgroup.zpowers (σ ^ (orderOf σ / f)) then 1 else 0) = 0 := by
      intro f hf
      obtain ⟨hfn, -⟩ := Nat.mem_divisors.mp hf
      have hf0 : f ≠ 0 := by
        rintro rfl
        exact hn0 (Nat.eq_zero_of_zero_dvd hfn)
      have h : y ∉ Subgroup.zpowers (σ ^ (orderOf σ / f)) := fun hmem =>
        hy ((mem_zpowers_pow_div_iff σ y hfn hf0).mp hmem).1
      simp [h]
    rw [Finset.sum_congr rfl hcong]
    simp [hy]

private theorem exists_pow_coprime_eq_of_orderOf_eq {σ y : G} (hmem : y ∈ Subgroup.zpowers σ)
    (hord : orderOf y = orderOf σ) :
    ∃ k : ℕ, k.Coprime (orderOf σ) ∧ σ ^ k = y := by
  obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hmem)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h1 : orderOf σ = 1 := by simpa using hord.symm
    exact ⟨1, Nat.coprime_one_left _, by simp [orderOf_eq_one_iff.mp h1]⟩
  · refine ⟨k, ?_, rfl⟩
    have h1 : orderOf (σ ^ k) = orderOf σ / Nat.gcd (orderOf σ) k := orderOf_pow' σ hk.ne'
    rw [hord] at h1
    have hgcd : Nat.gcd (orderOf σ) k = 1 := by
      by_contra hne
      have hpos : 0 < Nat.gcd (orderOf σ) k :=
        Nat.pos_of_ne_zero fun h0 => (orderOf_pos σ).ne'
          (Nat.eq_zero_of_gcd_eq_zero_left h0)
      have h4 : 1 < Nat.gcd (orderOf σ) k := lt_of_le_of_ne hpos (Ne.symm hne)
      exact absurd h1.symm (Nat.div_lt_self (orderOf_pos σ) h4).ne
    exact Nat.coprime_comm.mp hgcd

private theorem orderOf_pow_orderOf_div (σ : G) {f : ℕ} (hf : f ∣ orderOf σ) (hf0 : f ≠ 0) :
    orderOf (σ ^ (orderOf σ / f)) = f := by
  have hn0 : orderOf σ ≠ 0 := (orderOf_pos σ).ne'
  have hd0 : orderOf σ / f ≠ 0 :=
    Nat.div_ne_zero_iff.mpr ⟨hf0, Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hf⟩
  rw [orderOf_pow' σ hd0, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hf), Nat.div_div_self hf hn0]

omit [Finite G] in
private theorem ncard_conj_mem_eq_card_mul_ncard (H : Subgroup G) (τ : G) :
    {g : G | g⁻¹ * τ * g ∈ H}.ncard
      = Nat.card H * {x : G ⧸ H | τ • x = x}.ncard := by
  have hpre : {g : G | g⁻¹ * τ * g ∈ H}
      = (QuotientGroup.mk : G → G ⧸ H) ⁻¹' {x : G ⧸ H | τ • x = x} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    have hsmul : τ • (QuotientGroup.mk g : G ⧸ H) = QuotientGroup.mk (τ * g) :=
      MulAction.Quotient.smul_coe H τ g
    rw [hsmul, QuotientGroup.eq, show (τ * g)⁻¹ * g = (g⁻¹ * τ * g)⁻¹ by group]
    exact (inv_mem_iff).symm
  rw [← Nat.card_coe_set_eq, hpre,
    Nat.card_congr (QuotientGroup.preimageMkEquivSubgroupProdSet H _), Nat.card_prod,
    Nat.card_coe_set_eq]

open scoped Classical in
private theorem ncard_eq_sum_indicator {α : Type*} [Fintype α] (p : α → Prop) :
    ({a : α | p a}.ncard : ℤ) = ∑ a : α, (if p a then 1 else 0) := by
  rw [Finset.sum_boole]
  norm_cast
  rw [← Set.ncard_coe_finset (Finset.univ.filter p)]
  congr 1
  ext a
  simp

end Weight

end FrobeniusDensity

open scoped Classical in
theorem solution {G : Type*} [Group G] [Finite G] (σ : G) :
    0 < ∑ f ∈ (orderOf σ).divisors,
      (ArithmeticFunction.moebius (orderOf σ / f)) * (f : ℤ) := by
  open FrobeniusDensity in
  have hfin : Fintype G := Fintype.ofFinite G
  have hn0 : orderOf σ ≠ 0 := (orderOf_pos σ).ne'
  have hcard : ∀ f ∈ (orderOf σ).divisors,
      (f : ℤ) = ∑ y : G, (if y ∈ Subgroup.zpowers (σ ^ (orderOf σ / f)) then 1 else 0) := by
    intro f hf
    obtain ⟨hfn, -⟩ := Nat.mem_divisors.mp hf
    have hf0 : f ≠ 0 := by
      rintro rfl
      exact hn0 (Nat.eq_zero_of_zero_dvd hfn)
    rw [← ncard_eq_sum_indicator]
    norm_cast
    have h1 : {y : G | y ∈ Subgroup.zpowers (σ ^ (orderOf σ / f))}.ncard
        = Nat.card (Subgroup.zpowers (σ ^ (orderOf σ / f))) := by
      rw [← Nat.card_coe_set_eq]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun y => Iff.rfl)
    rw [h1, Nat.card_eq_fintype_card, Fintype.card_zpowers]
    exact (orderOf_pow_orderOf_div σ hfn hf0).symm
  calc (0 : ℤ) < if (σ : G) ∈ Subgroup.zpowers σ ∧ orderOf σ = orderOf σ then 1 else 0 := by
        simp [Subgroup.mem_zpowers]
    _ ≤ ∑ y : G, (if y ∈ Subgroup.zpowers σ ∧ orderOf y = orderOf σ then 1 else 0) := by
        refine Finset.single_le_sum (f := fun y : G =>
          (if y ∈ Subgroup.zpowers σ ∧ orderOf y = orderOf σ then (1:ℤ) else 0))
          (fun y _ => by positivity) (Finset.mem_univ σ)
    _ = ∑ y : G, ∑ f ∈ (orderOf σ).divisors, (ArithmeticFunction.moebius (orderOf σ / f)) *
          (if y ∈ Subgroup.zpowers (σ ^ (orderOf σ / f)) then 1 else 0) :=
        Finset.sum_congr rfl fun y _ => (sum_moebius_mem_zpowers σ y).symm
    _ = ∑ f ∈ (orderOf σ).divisors, ∑ y : G, (ArithmeticFunction.moebius (orderOf σ / f)) *
          (if y ∈ Subgroup.zpowers (σ ^ (orderOf σ / f)) then 1 else 0) := Finset.sum_comm
    _ = ∑ f ∈ (orderOf σ).divisors, (ArithmeticFunction.moebius (orderOf σ / f)) * (f : ℤ) := by
        refine Finset.sum_congr rfl fun f hf => ?_
        rw [hcard f hf, Finset.mul_sum]

end S_FrobeniusDensity_sum_moebius_mul_pos
end P2MW
export P2MW.S_FrobeniusDensity_sum_moebius_mul_pos (solution)
