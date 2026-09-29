-- Prove2me | solution 1 for CerednikDrinfeld.Omega.sum_add_eq_zero_of_isUnit_of_forall_v_apply_eq_mul_zpow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/ed9c7f4d-c206-5db8-83f1-c75cf2e19cf9

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_sum_add_eq_zero_of_isUnit_of_forall_v_apply_eq_mul_zpow

set_option autoImplicit false

p2m_open "CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_sum_add_eq_zero_of_isUnit_of_forall_v_apply_eq_mul_zpow.CerednikDrinfeld.Omega Polynomial"

noncomputable section

open Classical

namespace CerednikDrinfeld
namespace Omega
p2m_export "CerednikDrinfeld.Omega" "PseudoUniformizer affinoid affinoid_subset_upperHalfPlane mem_affinoid_iff' RatPair RatPair.evalAt vRestrict v_lt_iff_vRestrict_lt tendstoUniformly_iff_vRestrict restrictAffinoid holRing PseudoUniformizer.ϖ upperHalfPlane mem_upperHalfPlane_iff"
namespace Flow
p2m_open "CerednikDrinfeld.Omega CerednikDrinfeld"

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable (ϖ : PseudoUniformizer K₀ K)

local notation "𝔯" => Valued.v (algebraMap K₀ K (PseudoUniformizer.ϖ ϖ))
local notation "τ" => algebraMap K₀ K

theorem r_pos : 0 < 𝔯 := ϖ.pos
theorem r_lt_one : 𝔯 < 1 := ϖ.lt_one
theorem r_ne_zero : 𝔯 ≠ 0 := ϖ.pos.ne'
theorem one_lt_r_inv : 1 < 𝔯⁻¹ := (one_lt_inv₀ (r_pos ϖ)).2 (r_lt_one ϖ)
theorem r_le_r_inv : 𝔯 ≤ 𝔯⁻¹ := ((r_lt_one ϖ).trans (one_lt_r_inv ϖ)).le

section Unif

variable {ϖ}

theorem trichotomy (hunif : ∀ a : K₀, Valued.v (τ a) ≤ 𝔯 ∨ 1 ≤ Valued.v (τ a)) (a : K₀) :
    Valued.v (τ a) ≤ 𝔯 ∨ Valued.v (τ a) = 1 ∨ 𝔯⁻¹ ≤ Valued.v (τ a) := by
  rcases hunif a with h | h
  · exact Or.inl h
  have h0 : 0 < Valued.v (τ a) := lt_of_lt_of_le zero_lt_one h
  rcases hunif a⁻¹ with h' | h'
  · right; right
    rw [map_inv₀, map_inv₀] at h'
    exact inv_le_of_inv_le₀ h0 h'
  · right; left
    rw [map_inv₀, map_inv₀] at h'
    exact le_antisymm ((one_le_inv₀ h0).mp h') h

theorem le_one_or (hunif : ∀ a : K₀, Valued.v (τ a) ≤ 𝔯 ∨ 1 ≤ Valued.v (τ a)) (a : K₀) :
    Valued.v (τ a) ≤ 1 ∨ 𝔯⁻¹ ≤ Valued.v (τ a) := by
  rcases trichotomy hunif a with h | h | h
  · exact Or.inl (h.trans (r_lt_one ϖ).le)
  · exact Or.inl h.le
  · exact Or.inr h

theorem exists_rep (hunif : ∀ a : K₀, Valued.v (τ a) ≤ 𝔯 ∨ 1 ≤ Valued.v (τ a))
    (T : Finset K₀) (hTcov : ∀ a : K₀, Valued.v (τ a) ≤ 1 → ∃ t ∈ T, Valued.v (τ a - τ t) < 1)
    {a : K₀} (ha : Valued.v (τ a) ≤ 1) : ∃ t ∈ T, Valued.v (τ a - τ t) ≤ 𝔯 := by
  obtain ⟨t, ht, hlt⟩ := hTcov a ha
  refine ⟨t, ht, ?_⟩
  rcases hunif (a - t) with h | h
  · rwa [map_sub] at h
  · rw [map_sub] at h; exact absurd hlt (not_lt.2 h)

theorem ne_algebraMap_of_between (hunif : ∀ a : K₀, Valued.v (τ a) ≤ 𝔯 ∨ 1 ≤ Valued.v (τ a))
    {y : K} (h1 : 𝔯 < Valued.v y) (h2 : Valued.v y < 1) (a : K₀) : τ a ≠ y := by
  rintro rfl
  rcases hunif a with h | h
  · exact absurd h1 (not_lt.2 h)
  · exact absurd h2 (not_lt.2 h)

theorem mem_affinoid_one_of_star (hunif : ∀ a : K₀, Valued.v (τ a) ≤ 𝔯 ∨ 1 ≤ Valued.v (τ a))
    (T : Finset K₀) (hTcov : ∀ a : K₀, Valued.v (τ a) ≤ 1 → ∃ t ∈ T, Valued.v (τ a - τ t) < 1)
    {z : K} (hS1 : ∀ t ∈ T, 𝔯 < Valued.v (z - τ t)) (hS2 : Valued.v z < 𝔯⁻¹) : z ∈ affinoid ϖ 1 := by
  rw [mem_affinoid_iff', pow_one, pow_one]
  refine ⟨hS2.le, fun a => ?_⟩
  rcases le_one_or hunif a with ha | ha
  · obtain ⟨t, ht, hat⟩ := exists_rep hunif T hTcov ha
    have hlt : Valued.v (τ a - τ t) < Valued.v (z - τ t) := hat.trans_lt (hS1 t ht)
    have : z - τ a = (z - τ t) - (τ a - τ t) := by ring
    rw [this, Valuation.map_sub_eq_of_lt_left _ hlt]
    exact (hS1 t ht).le
  · have hlt : Valued.v z < Valued.v (τ a) := hS2.trans_le ha
    rw [Valuation.map_sub_eq_of_lt_right _ hlt]
    exact (r_le_r_inv ϖ).trans ha

theorem inf_or_disc_of_not_mem (hunif : ∀ a : K₀, Valued.v (τ a) ≤ 𝔯 ∨ 1 ≤ Valued.v (τ a))
    (T : Finset K₀) (hTcov : ∀ a : K₀, Valued.v (τ a) ≤ 1 → ∃ t ∈ T, Valued.v (τ a - τ t) < 1)
    {w : K} (hw : w ∉ affinoid ϖ 1) : 𝔯⁻¹ ≤ Valued.v w ∨ ∃ t ∈ T, Valued.v (w - τ t) ≤ 𝔯 := by
  by_cases hw1 : Valued.v w ≤ 𝔯⁻¹
  · have h : ¬ ∀ a : K₀, Valued.v (τ a) ≤ 𝔯⁻¹ ^ 1 → 𝔯 ^ 1 ≤ Valued.v (w - τ a) :=
      fun h => hw ⟨by rwa [pow_one], h⟩
    push Not at h
    obtain ⟨a, ha, hlt⟩ := h
    rw [pow_one] at ha hlt
    rcases le_one_or hunif a with h | h
    · obtain ⟨t, ht, hat⟩ := exists_rep hunif T hTcov h
      refine Or.inr ⟨t, ht, ?_⟩
      have : w - τ t = (w - τ a) + (τ a - τ t) := by ring
      rw [this]
      exact Valuation.map_add_le _ hlt.le hat
    · left
      have heq : Valued.v (τ a) = 𝔯⁻¹ := le_antisymm ha h
      have hlt' : Valued.v (w - τ a) < Valued.v (τ a) := by
        rw [heq]; exact hlt.trans_le (r_le_r_inv ϖ)
      have : w = (w - τ a) + τ a := by ring
      rw [this, Valuation.map_add_eq_of_lt_right _ hlt', heq]
  · exact Or.inl (not_le.1 hw1).le

end Unif

theorem exists_ratPair_v_evalAt_eq (f : ↥(holRing ϖ)) (hf : IsUnit f) (n : ℕ) :
    ∃ r : RatPair K, r.IsPoleFreeOn (affinoid ϖ n) ∧
      ∀ z : ↥(affinoid ϖ n), Valued.v (r.evalAt z) = Valued.v (restrictAffinoid ϖ n (f : ↥(upperHalfPlane K₀ K) → K) z) := by
  obtain ⟨g, hfg⟩ := hf.exists_right_inv

  have hpt : ∀ z : ↥(upperHalfPlane K₀ K),
      (f : ↥(upperHalfPlane K₀ K) → K) z * (g : ↥(upperHalfPlane K₀ K) → K) z = 1 := fun z => by
    have := congrArg (fun h : ↥(holRing ϖ) => (h : ↥(upperHalfPlane K₀ K) → K) z) hfg
    simpa using this
  obtain ⟨r, hr, -, hlim⟩ := f.2 n
  obtain ⟨B, hB⟩ := (g.2 n).bounded
  by_cases hB0 : B = 0
  ·
    refine ⟨r 0, hr 0, fun z => ?_⟩
    have hg0 : (g : ↥(upperHalfPlane K₀ K) → K) (Set.inclusion (affinoid_subset_upperHalfPlane ϖ n) z) = 0 := by
      have := hB z
      rw [hB0, map_zero, le_zero_iff, map_eq_zero] at this
      exact this
    have := hpt (Set.inclusion (affinoid_subset_upperHalfPlane ϖ n) z)
    rw [hg0, mul_zero] at this
    exact absurd this zero_ne_one

  have hlow : ∀ z : ↥(affinoid ϖ n), Valued.v B⁻¹ ≤
      Valued.v (restrictAffinoid ϖ n (f : ↥(upperHalfPlane K₀ K) → K) z) := fun z => by
    have h1 := hpt (Set.inclusion (affinoid_subset_upperHalfPlane ϖ n) z)
    have hgz := hB z
    have hf1 : Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) (Set.inclusion (affinoid_subset_upperHalfPlane ϖ n) z)) =
        (Valued.v ((g : ↥(upperHalfPlane K₀ K) → K) (Set.inclusion (affinoid_subset_upperHalfPlane ϖ n) z)))⁻¹ := by
      have := congrArg Valued.v h1
      rw [map_mul, map_one] at this
      exact eq_inv_of_mul_eq_one_left this
    have hgpos : 0 < Valued.v ((g : ↥(upperHalfPlane K₀ K) → K) (Set.inclusion (affinoid_subset_upperHalfPlane ϖ n) z)) := by
      rw [Valuation.pos_iff]
      intro h0
      rw [h0, mul_zero] at h1
      exact zero_ne_one h1
    change Valued.v B⁻¹ ≤ Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) (Set.inclusion (affinoid_subset_upperHalfPlane ϖ n) z))
    rw [hf1, map_inv₀]
    exact inv_anti₀ hgpos hgz

  have hBinv : vRestrict K B⁻¹ ≠ 0 := by
    rw [Valuation.ne_zero_iff]; exact inv_ne_zero hB0
  rw [tendstoUniformly_iff_vRestrict] at hlim
  obtain ⟨k, hk⟩ := (hlim (Units.mk0 _ hBinv)).exists
  refine ⟨r k, hr k, fun z => ?_⟩
  have hlt : Valued.v ((r k).evalAt z - restrictAffinoid ϖ n (f : ↥(upperHalfPlane K₀ K) → K) z) < Valued.v B⁻¹ := by
    rw [v_lt_iff_vRestrict_lt]
    exact hk z
  exact Valuation.map_eq_of_sub_lt _ (hlt.trans_le (hlow z))

theorem apply_ne_zero_of_isUnit (f : ↥(holRing ϖ)) (hf : IsUnit f) (z : ↥(upperHalfPlane K₀ K)) :
    (f : ↥(upperHalfPlane K₀ K) → K) z ≠ 0 := by
  intro h0
  obtain ⟨g, hfg⟩ := hf.exists_right_inv
  have := congrArg (fun h : ↥(holRing ϖ) => (h : ↥(upperHalfPlane K₀ K) → K) z) hfg
  rw [show ((f * g : ↥(holRing ϖ)) : ↥(upperHalfPlane K₀ K) → K) z =
    (f : ↥(upperHalfPlane K₀ K) → K) z * (g : ↥(upperHalfPlane K₀ K) → K) z from rfl, h0, zero_mul] at this
  exact zero_ne_one this

theorem prod_pow_update (T : Finset K₀) (x : K₀ → Γ₀) (n : K₀ → ℕ) {t₀ : K₀} (h : t₀ ∈ T) :
    ∏ t ∈ T, x t ^ Function.update n t₀ (n t₀ + 1) t = x t₀ * ∏ t ∈ T, x t ^ n t := by
  rw [← Finset.mul_prod_erase T _ h, ← Finset.mul_prod_erase T (fun t => x t ^ n t) h, Function.update_self, pow_succ]
  have : ∏ t ∈ T.erase t₀, x t ^ Function.update n t₀ (n t₀ + 1) t = ∏ t ∈ T.erase t₀, x t ^ n t :=
    Finset.prod_congr rfl fun t ht => by rw [Function.update_of_ne (Finset.ne_of_mem_erase ht)]
  rw [this, mul_comm (x t₀ ^ n t₀) (x t₀), mul_assoc]

theorem prod_zpow_eq_zpow_sum (T : Finset K₀) {x : Γ₀} (hx : x ≠ 0) (n : K₀ → ℤ) :
    ∏ t ∈ T, x ^ n t = x ^ ∑ t ∈ T, n t := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hx]

section Star

variable {ϖ}

theorem exists_v_multiset_prod_eq (hunif : ∀ a : K₀, Valued.v (τ a) ≤ 𝔯 ∨ 1 ≤ Valued.v (τ a))
    (T : Finset K₀) (hTcov : ∀ a : K₀, Valued.v (τ a) ≤ 1 → ∃ t ∈ T, Valued.v (τ a - τ t) < 1)
    (S : Multiset K) (hS : ∀ α ∈ S, α ∉ affinoid ϖ 1) :
    ∃ (c : Γ₀) (n : K₀ → ℕ), ∀ z : K, (∀ t ∈ T, 𝔯 < Valued.v (z - τ t)) → Valued.v z < 𝔯⁻¹ →
      Valued.v (S.map (fun α => z - α)).prod = c * ∏ t ∈ T, Valued.v (z - τ t) ^ n t := by
  induction S using Multiset.induction_on with
  | empty => exact ⟨1, fun _ => 0, fun z _ _ => by simp⟩
  | cons α S ih =>
    obtain ⟨c, n, h⟩ := ih (fun β hβ => hS β (Multiset.mem_cons_of_mem hβ))
    have hα : α ∉ affinoid ϖ 1 := hS α (Multiset.mem_cons_self α S)
    rcases inf_or_disc_of_not_mem hunif T hTcov hα with hinf | ⟨t₀, ht₀, hdisc⟩
    · refine ⟨Valued.v α * c, n, fun z hS1 hS2 => ?_⟩
      rw [Multiset.map_cons, Multiset.prod_cons, map_mul, h z hS1 hS2,
        Valuation.map_sub_eq_of_lt_right _ (hS2.trans_le hinf), mul_assoc]
    · refine ⟨c, Function.update n t₀ (n t₀ + 1), fun z hS1 hS2 => ?_⟩
      rw [Multiset.map_cons, Multiset.prod_cons, map_mul, h z hS1 hS2, prod_pow_update T _ n ht₀]
      have : z - α = (z - τ t₀) - (α - τ t₀) := by ring
      rw [this, Valuation.map_sub_eq_of_lt_left _ (hdisc.trans_lt (hS1 t₀ ht₀)), mul_left_comm]

theorem exists_v_eval_eq [IsAlgClosed K] (hunif : ∀ a : K₀, Valued.v (τ a) ≤ 𝔯 ∨ 1 ≤ Valued.v (τ a))
    (T : Finset K₀) (hTcov : ∀ a : K₀, Valued.v (τ a) ≤ 1 → ∃ t ∈ T, Valued.v (τ a - τ t) < 1)
    (p : K[X]) (hp : ∀ α ∈ p.roots, α ∉ affinoid ϖ 1) :
    ∃ (c : Γ₀) (n : K₀ → ℕ), ∀ z : K, (∀ t ∈ T, 𝔯 < Valued.v (z - τ t)) → Valued.v z < 𝔯⁻¹ →
      Valued.v (p.eval z) = c * ∏ t ∈ T, Valued.v (z - τ t) ^ n t := by
  obtain ⟨c, n, h⟩ := exists_v_multiset_prod_eq hunif T hTcov p.roots hp
  refine ⟨Valued.v p.leadingCoeff * c, n, fun z hS1 hS2 => ?_⟩
  have hsplit := (IsAlgClosed.splits p).eq_prod_roots
  conv_lhs => rw [hsplit]
  rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map, map_mul]
  have : (Multiset.map (eval z ∘ fun x => X - C x) p.roots) = Multiset.map (fun α => z - α) p.roots := by
    refine Multiset.map_congr rfl fun α _ => ?_
    simp
  rw [this, h z hS1 hS2, mul_assoc]

theorem exists_v_div_eq [IsAlgClosed K] (hunif : ∀ a : K₀, Valued.v (τ a) ≤ 𝔯 ∨ 1 ≤ Valued.v (τ a))
    (T : Finset K₀) (hTcov : ∀ a : K₀, Valued.v (τ a) ≤ 1 → ∃ t ∈ T, Valued.v (τ a - τ t) < 1)
    (p q : K[X]) (hp : ∀ α ∈ p.roots, α ∉ affinoid ϖ 1)
    (hq : ∀ α ∈ q.roots, α ∉ affinoid ϖ 1) :
    ∃ (c : Γ₀) (n : K₀ → ℤ), ∀ z : K, (∀ t ∈ T, 𝔯 < Valued.v (z - τ t)) → Valued.v z < 𝔯⁻¹ →
      Valued.v (p.eval z / q.eval z) = c * ∏ t ∈ T, Valued.v (z - τ t) ^ n t := by
  obtain ⟨cp, np, hP⟩ := exists_v_eval_eq hunif T hTcov p hp
  obtain ⟨cq, nq, hQ⟩ := exists_v_eval_eq hunif T hTcov q hq
  refine ⟨cp / cq, fun t => (np t : ℤ) - (nq t : ℤ), fun z hS1 hS2 => ?_⟩
  rw [map_div₀, hP z hS1 hS2, hQ z hS1 hS2, mul_div_mul_comm, ← Finset.prod_div_distrib]
  refine congrArg (cp / cq * ·) (Finset.prod_congr rfl fun t ht => ?_)
  have h0 : Valued.v (z - τ t) ≠ 0 := ((r_pos ϖ).trans (hS1 t ht)).ne'
  dsimp only
  rw [zpow_sub₀ h0, zpow_natCast, zpow_natCast]

end Star

theorem zpow_exponent_eq {c c' x₁ x₂ : Γ₀} {k k' : ℤ} (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0) (hne : x₁ ≠ x₂)
    (h0 : c * x₁ ^ k ≠ 0) (h₁ : c * x₁ ^ k = c' * x₁ ^ k') (h₂ : c * x₂ ^ k = c' * x₂ ^ k') : k = k' := by
  have hc' : c' ≠ 0 := by rw [h₁] at h0; exact left_ne_zero_of_mul h0
  have e : ∀ {x : Γ₀}, x ≠ 0 → c * x ^ k = c' * x ^ k' → x ^ (k' - k) = c / c' := fun {x} hx h => by
    rw [zpow_sub₀ hx, div_eq_div_iff (zpow_ne_zero _ hx) hc', mul_comm]
    exact h.symm
  have h12 : (x₁ / x₂) ^ (k' - k) = 1 := by
    rw [div_zpow, e hx₁ h₁, e hx₂ h₂, div_self (div_ne_zero (left_ne_zero_of_mul h0) hc')]
  have hu0 : 0 < x₁ / x₂ := zero_lt_iff.mpr (div_ne_zero hx₁ hx₂)
  have hu1 : x₁ / x₂ ≠ 1 := by rwa [Ne, div_eq_one_iff_eq hx₂]
  have := zpow_right_injective₀ hu0 hu1 (h12.trans (zpow_zero _).symm)
  omega

theorem exists_two_radii [IsAlgClosed K] : ∃ y₂ y₃ : K,
    𝔯 < Valued.v y₂ ∧ Valued.v y₂ < 1 ∧ 𝔯 < Valued.v y₃ ∧ Valued.v y₃ < 1 ∧ Valued.v y₂ ≠ Valued.v y₃ := by
  obtain ⟨y₂, hy₂⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K₀ K ϖ.ϖ) (show 0 < 2 by norm_num)
  obtain ⟨y₃, hy₃⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K₀ K ϖ.ϖ) (show 0 < 3 by norm_num)
  have h2 : Valued.v y₂ ^ 2 = 𝔯 := by rw [← map_pow, hy₂]
  have h3 : Valued.v y₃ ^ 3 = 𝔯 := by rw [← map_pow, hy₃]
  have hs0 : 0 < Valued.v y₂ := by
    rw [Valuation.pos_iff]; rintro rfl; rw [zero_pow two_ne_zero] at hy₂; exact (r_ne_zero ϖ) (by rw [← hy₂, map_zero])
  have hu0 : 0 < Valued.v y₃ := by
    rw [Valuation.pos_iff]; rintro rfl; rw [zero_pow three_ne_zero] at hy₃; exact (r_ne_zero ϖ) (by rw [← hy₃, map_zero])
  have hs1 : Valued.v y₂ < 1 := by
    by_contra h; rw [not_lt] at h
    have h' : 1 ≤ Valued.v y₂ ^ 2 := one_le_pow₀ h
    rw [h2] at h'
    exact absurd (r_lt_one ϖ) (not_lt.2 h')
  have hu1 : Valued.v y₃ < 1 := by
    by_contra h; rw [not_lt] at h
    have h' : 1 ≤ Valued.v y₃ ^ 3 := one_le_pow₀ h
    rw [h3] at h'
    exact absurd (r_lt_one ϖ) (not_lt.2 h')
  refine ⟨y₂, y₃, ?_, hs1, ?_, hu1, fun heq => ?_⟩
  · rw [← h2, pow_two]
    calc Valued.v y₂ * Valued.v y₂ < Valued.v y₂ * 1 := mul_lt_mul_of_pos_left hs1 hs0
      _ = Valued.v y₂ := mul_one _
  · rw [← h3, pow_succ, pow_two]
    calc Valued.v y₃ * Valued.v y₃ * Valued.v y₃ < 1 * Valued.v y₃ := by
          refine mul_lt_mul_of_pos_right ?_ hu0
          calc Valued.v y₃ * Valued.v y₃ < Valued.v y₃ * 1 := mul_lt_mul_of_pos_left hu1 hu0
            _ = Valued.v y₃ := mul_one _
            _ < 1 := hu1
      _ = Valued.v y₃ := one_mul _
  ·
    rw [heq] at h2
    have : Valued.v y₃ ^ 2 * Valued.v y₃ = Valued.v y₃ ^ 2 * 1 := by rw [mul_one, ← pow_succ, h3, h2]
    have := mul_left_cancel₀ (pow_ne_zero 2 hu0.ne') this
    exact absurd hu1 (by rw [this]; exact lt_irrefl 1)

end CerednikDrinfeld.Omega.Flow

end

open _root_.CerednikDrinfeld.Omega _root_.P2MW.S_CerednikDrinfeld_Omega_sum_add_eq_zero_of_isUnit_of_forall_v_apply_eq_mul_zpow.CerednikDrinfeld.Omega CerednikDrinfeld.Omega.Flow in
theorem solution
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hunif : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ∨ 1 ≤ Valued.v (algebraMap K₀ K a))
    (T : Finset K₀) (hT : ∀ t ∈ T, Valued.v (algebraMap K₀ K t) ≤ 1)
    (hTcov : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < 1)
    (hTsep : ∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → 1 ≤ Valued.v (algebraMap K₀ K t - algebraMap K₀ K t'))
    (f : ↥(holRing ϖ)) (hf : IsUnit f) (m : K₀ → ℤ) (mInf : ℤ)
    (hm : ∀ t ∈ T, ∃ c : Γ₀, ∀ z : ↥(upperHalfPlane K₀ K),
      Valued.v (algebraMap K₀ K ϖ.ϖ) < Valued.v ((z : K) - algebraMap K₀ K t) →
      Valued.v ((z : K) - algebraMap K₀ K t) < 1 →
        Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) z) = c * Valued.v ((z : K) - algebraMap K₀ K t) ^ (m t))
    (hmInf : ∃ c : Γ₀, ∀ z : ↥(upperHalfPlane K₀ K),
      Valued.v (algebraMap K₀ K ϖ.ϖ) < (Valued.v (z : K))⁻¹ → (Valued.v (z : K))⁻¹ < 1 →
        Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) z) = c * (Valued.v (z : K))⁻¹ ^ mInf) :
    (∑ t ∈ T, m t) + mInf = 0 ∧
    ∃ c₀ : Γ₀, ∀ z : ↥(upperHalfPlane K₀ K),
      (∀ t ∈ T, Valued.v (algebraMap K₀ K ϖ.ϖ) < Valued.v ((z : K) - algebraMap K₀ K t)) →
      Valued.v (z : K) < (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ →
        Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) z) =
          c₀ * ∏ t ∈ T, Valued.v ((z : K) - algebraMap K₀ K t) ^ (m t) := by
  classical

  obtain ⟨r, hr, hrf⟩ := exists_ratPair_v_evalAt_eq ϖ f hf 1
  have hfr : ∀ (z : ↥(upperHalfPlane K₀ K)) (h1 : (z : K) ∈ affinoid ϖ 1),
      Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) z) = Valued.v (r.evalAt z) := fun z h1 => (hrf ⟨z, h1⟩).symm

  have hval : ∀ z ∈ affinoid ϖ 1, r.evalAt z ≠ 0 := fun z h1 h0 => by
    have := hrf ⟨z, h1⟩
    rw [h0, map_zero, eq_comm, map_eq_zero] at this
    exact apply_ne_zero_of_isUnit ϖ f hf _ this
  have hp : ∀ α ∈ r.num.roots, α ∉ affinoid ϖ 1 := fun α hα h1 =>
    hval α h1 (by rw [RatPair.evalAt, (mem_roots'.1 hα).2, zero_div])
  have hq : ∀ α ∈ r.den.roots, α ∉ affinoid ϖ 1 := fun α hα h1 => hr α h1 (mem_roots'.1 hα).2

  obtain ⟨C, n, hstar⟩ := exists_v_div_eq hunif T hTcov r.num r.den hp hq
  have hfS : ∀ z : ↥(upperHalfPlane K₀ K),
      (∀ t ∈ T, Valued.v (algebraMap K₀ K ϖ.ϖ) < Valued.v ((z : K) - algebraMap K₀ K t)) →
      Valued.v (z : K) < (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ →
        Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) z) =
          C * ∏ t ∈ T, Valued.v ((z : K) - algebraMap K₀ K t) ^ (n t) := fun z hS1 hS2 => by
    rw [hfr z (mem_affinoid_one_of_star hunif T hTcov hS1 hS2)]
    exact hstar z hS1 hS2
  have hfne : ∀ z : ↥(upperHalfPlane K₀ K), Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) z) ≠ 0 := fun z => by
    rw [Valuation.ne_zero_iff]; exact apply_ne_zero_of_isUnit ϖ f hf z

  obtain ⟨y₂, y₃, h2a, h2b, h3a, h3b, h23⟩ := exists_two_radii ϖ
  have hy0 : ∀ {y : K}, Valued.v (algebraMap K₀ K ϖ.ϖ) < Valued.v y → y ≠ 0 := fun {y} h h0 => by
    rw [h0, map_zero] at h; exact not_lt.2 zero_le' h

  have hmt : ∀ t ∈ T, m t = n t := by
    intro t ht
    obtain ⟨ct, hct⟩ := hm t ht

    set D : Γ₀ := ∏ t' ∈ T.erase t, Valued.v (algebraMap K₀ K t - algebraMap K₀ K t') ^ (n t') with hD

    have key : ∀ {y : K}, Valued.v (algebraMap K₀ K ϖ.ϖ) < Valued.v y → Valued.v y < 1 →
        ct * Valued.v y ^ (m t) ≠ 0 ∧ ct * Valued.v y ^ (m t) = (C * D) * Valued.v y ^ (n t) := by
      intro y hy1 hy2
      have hzΩ : algebraMap K₀ K t + y ∈ upperHalfPlane K₀ K := by
        rw [mem_upperHalfPlane_iff]
        intro a h
        apply ne_algebraMap_of_between hunif hy1 hy2 (a - t)
        rw [map_sub, h]; ring
      set z : ↥(upperHalfPlane K₀ K) := ⟨_, hzΩ⟩ with hz
      have hzt : (z : K) - algebraMap K₀ K t = y := by simp [hz]
      have hzt' : ∀ t' ∈ T.erase t, Valued.v ((z : K) - algebraMap K₀ K t') =
          Valued.v (algebraMap K₀ K t - algebraMap K₀ K t') := fun t' ht' => by
        have hne : t ≠ t' := (Finset.ne_of_mem_erase ht').symm
        have h1 : Valued.v y < Valued.v (algebraMap K₀ K t - algebraMap K₀ K t') :=
          hy2.trans_le (hTsep t ht t' (Finset.mem_of_mem_erase ht') hne)
        have : (z : K) - algebraMap K₀ K t' = (algebraMap K₀ K t - algebraMap K₀ K t') + y := by
          simp [hz]; ring
        rw [this, Valuation.map_add_eq_of_lt_left _ h1]
      have hS1 : ∀ t' ∈ T, Valued.v (algebraMap K₀ K ϖ.ϖ) < Valued.v ((z : K) - algebraMap K₀ K t') := by
        intro t' ht'
        by_cases htt : t' = t
        · rw [htt, hzt]; exact hy1
        · rw [hzt' t' (Finset.mem_erase.2 ⟨htt, ht'⟩)]
          exact (r_lt_one ϖ).trans_le (hTsep t ht t' ht' (Ne.symm htt))
      have hS2 : Valued.v (z : K) < (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ := by
        have : (z : K) = y + algebraMap K₀ K t := by simp [hz]; ring
        rw [this]
        exact (Valuation.map_add_le _ hy2.le (hT t ht)).trans_lt (one_lt_r_inv ϖ)
      have e1 := hct z (by rw [hzt]; exact hy1) (by rw [hzt]; exact hy2)
      have e2 := hfS z hS1 hS2
      rw [← Finset.mul_prod_erase T _ ht, hzt,
        Finset.prod_congr rfl (fun t' ht' => by rw [hzt' t' ht']), ← hD] at e2
      rw [hzt] at e1
      refine ⟨by rw [← e1]; exact hfne z, ?_⟩
      rw [← e1, e2, mul_comm (Valued.v y ^ n t) D, ← mul_assoc]
    have hv0 : ∀ {y : K}, Valued.v (algebraMap K₀ K ϖ.ϖ) < Valued.v y → Valued.v y ≠ 0 := fun h => ((r_pos ϖ).trans h).ne'
    exact zpow_exponent_eq (hv0 h2a) (hv0 h3a) h23 (key h2a h2b).1 (key h2a h2b).2 (key h3a h3b).2

  have hmInf' : mInf = -∑ t ∈ T, n t := by
    obtain ⟨ci, hci⟩ := hmInf
    have key : ∀ {y : K}, Valued.v (algebraMap K₀ K ϖ.ϖ) < Valued.v y → Valued.v y < 1 →
        ci * Valued.v y ^ mInf ≠ 0 ∧ ci * Valued.v y ^ mInf = C * Valued.v y ^ (-∑ t ∈ T, n t) := by
      intro y hy1 hy2
      have hyv0 : Valued.v y ≠ 0 := ((r_pos ϖ).trans hy1).ne'
      have hy0' : y ≠ 0 := fun h => hyv0 (by rw [h, map_zero])
      have hwΩ : y⁻¹ ∈ upperHalfPlane K₀ K := by
        rw [mem_upperHalfPlane_iff]
        intro a h
        have ha : a ≠ 0 := fun ha => hy0' (inv_eq_zero.mp (by rw [← h, ha, map_zero]))
        apply ne_algebraMap_of_between hunif hy1 hy2 a⁻¹
        rw [map_inv₀, h, inv_inv]
      set w : ↥(upperHalfPlane K₀ K) := ⟨_, hwΩ⟩ with hw
      have hvw : Valued.v (w : K) = (Valued.v y)⁻¹ := by simp [hw]
      have hvw1 : 1 < Valued.v (w : K) := by rw [hvw]; exact (one_lt_inv₀ ((r_pos ϖ).trans hy1)).2 hy2
      have hwt : ∀ t' ∈ T, Valued.v ((w : K) - algebraMap K₀ K t') = Valued.v (w : K) := fun t' ht' =>
        Valuation.map_sub_eq_of_lt_left _ ((hT t' ht').trans_lt hvw1)
      have hS1 : ∀ t' ∈ T, Valued.v (algebraMap K₀ K ϖ.ϖ) < Valued.v ((w : K) - algebraMap K₀ K t') := fun t' ht' => by
        rw [hwt t' ht']; exact (r_lt_one ϖ).trans hvw1
      have hS2 : Valued.v (w : K) < (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ := by
        rw [hvw]; exact inv_strictAnti₀ (r_pos ϖ) hy1
      have e1 := hci w (by rw [hvw, inv_inv]; exact hy1) (by rw [hvw, inv_inv]; exact hy2)
      have e2 := hfS w hS1 hS2
      rw [Finset.prod_congr rfl (fun t' ht' => by rw [hwt t' ht']), prod_zpow_eq_zpow_sum T (by rw [hvw]; exact inv_ne_zero hyv0),
        hvw, inv_zpow'] at e2
      rw [hvw, inv_inv] at e1
      refine ⟨by rw [← e1]; exact hfne w, ?_⟩
      rw [← e1, e2]
    have hv0 : ∀ {y : K}, Valued.v (algebraMap K₀ K ϖ.ϖ) < Valued.v y → Valued.v y ≠ 0 := fun h => ((r_pos ϖ).trans h).ne'
    exact zpow_exponent_eq (hv0 h2a) (hv0 h3a) h23 (key h2a h2b).1 (key h2a h2b).2 (key h3a h3b).2

  refine ⟨?_, C, fun z hS1 hS2 => ?_⟩
  · rw [hmInf', Finset.sum_congr rfl (fun t ht => hmt t ht)]; ring
  · rw [hfS z hS1 hS2]
    exact congrArg (C * ·) (Finset.prod_congr rfl fun t ht => by rw [hmt t ht])

end S_CerednikDrinfeld_Omega_sum_add_eq_zero_of_isUnit_of_forall_v_apply_eq_mul_zpow
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_sum_add_eq_zero_of_isUnit_of_forall_v_apply_eq_mul_zpow (solution)
