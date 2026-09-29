-- Prove2me | solution 1 for CerednikDrinfeld.Omega.v_apply_mul_inv_eq_mul_zpow_neg_sum_of_star
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/f87e80af-33ad-531d-88e5-423859e091f2

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_v_apply_mul_inv_eq_mul_zpow_neg_sum_of_star

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.Omega

namespace UAPEdge

variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀]

theorem eq_of_two_radii {A B x₁ x₂ : Γ₀} (hB : B ≠ 0) (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0) (hne : x₁ ≠ x₂)
    {M S : ℤ} (h₁ : A * x₁ ^ M = B * x₁ ^ S) (h₂ : A * x₂ ^ M = B * x₂ ^ S) : A = B := by
  have hA : A ≠ 0 := by
    rintro rfl
    rw [zero_mul] at h₁
    exact (mul_ne_zero hB (zpow_ne_zero S hx₁)) h₁.symm

  have hq : (x₁ / x₂) ^ (M - S) = 1 := by
    have e1 : x₁ ^ (M - S) = B / A := by
      rw [zpow_sub₀ hx₁, eq_div_iff hA, div_mul_eq_mul_div, div_eq_iff (zpow_ne_zero S hx₁), mul_comm, h₁, mul_comm]
    have e2 : x₂ ^ (M - S) = B / A := by
      rw [zpow_sub₀ hx₂, eq_div_iff hA, div_mul_eq_mul_div, div_eq_iff (zpow_ne_zero S hx₂), mul_comm, h₂, mul_comm]
    rw [div_zpow, e1, e2, div_self (div_ne_zero hB hA)]
  have hr0 : 0 < x₁ / x₂ := div_pos (zero_lt_iff.mpr hx₁) (zero_lt_iff.mpr hx₂)
  have hr1 : x₁ / x₂ ≠ 1 := fun h => hne (by rwa [div_eq_one_iff_eq hx₂] at h)
  have hMS : M - S = 0 := by
    rcases lt_or_gt_of_ne hr1 with hlt | hgt
    · exact (zpow_right_strictAnti₀ hr0 hlt).injective (hq.trans (zpow_zero _).symm)
    · exact (zpow_right_strictMono₀ hgt).injective (hq.trans (zpow_zero _).symm)
  have hMS' : M = S := by omega
  subst hMS'
  exact mul_right_cancel₀ (zpow_ne_zero M hx₁) h₁

end UAPEdge

open scoped MatrixGroups

theorem solution
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hunif : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ∨ 1 ≤ Valued.v (algebraMap K₀ K a))
    (T : Finset K₀) (hT : ∀ t ∈ T, Valued.v (algebraMap K₀ K t) ≤ 1)
    (hTcov : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < 1)
    (hTsep : ∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → 1 ≤ Valued.v (algebraMap K₀ K t - algebraMap K₀ K t'))
    (F : K → K) (c₀ c₀' : Γ₀) (m m' : K₀ → ℤ)
    (hstar : ∀ z : K, (∀ t ∈ T, Valued.v (algebraMap K₀ K ϖ.ϖ) < Valued.v (z - algebraMap K₀ K t)) →
      Valued.v z < (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ →
        Valued.v (F z) = c₀ * ∏ t ∈ T, Valued.v (z - algebraMap K₀ K t) ^ (m t))
    (hstar' : ∀ w : K, (∀ t ∈ T, Valued.v (algebraMap K₀ K ϖ.ϖ) < Valued.v (w - algebraMap K₀ K t)) →
      Valued.v w < (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ →
        Valued.v (F (w * (algebraMap K₀ K ϖ.ϖ)⁻¹)) = c₀' * ∏ t ∈ T, Valued.v (w - algebraMap K₀ K t) ^ (m' t))
    (w w' : K) (hw : w ∈ affinoid ϖ 0) (hw' : w' ∈ affinoid ϖ 0) :
    Valued.v (F (w * (algebraMap K₀ K ϖ.ϖ)⁻¹)) =
      Valued.v (F w') * Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (-(∑ t ∈ T, m t)) := by
  classical
  have hzsum : ∀ (a : Γ₀), a ≠ 0 → ∀ (s : Finset K₀) (k : K₀ → ℤ), ∏ t ∈ s, a ^ k t = a ^ ∑ t ∈ s, k t := by
    intro a ha s k
    induction s using Finset.induction_on with
    | empty => simp
    | insert x s hx ih => rw [Finset.prod_insert hx, Finset.sum_insert hx, ih, zpow_add₀ ha]

  have hp0 : 0 < Valued.v (algebraMap K₀ K ϖ.ϖ) := ϖ.pos
  have hp1 : Valued.v (algebraMap K₀ K ϖ.ϖ) < 1 := ϖ.lt_one
  have hpne : Valued.v (algebraMap K₀ K ϖ.ϖ) ≠ 0 := hp0.ne'
  have hpinv : 1 < (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ := (one_lt_inv₀ hp0).mpr hp1
  have hϖK : algebraMap K₀ K ϖ.ϖ ≠ 0 := (Valuation.ne_zero_iff _).mp hpne

  have fib : ∀ {x : K}, x ∈ affinoid ϖ 0 → Valued.v x ≤ 1 ∧ ∀ t ∈ T, Valued.v (x - algebraMap K₀ K t) = 1 := by
    intro x hx
    rw [mem_affinoid_iff'] at hx
    obtain ⟨hx1, hx2⟩ := hx
    simp only [pow_zero] at hx1 hx2
    refine ⟨hx1, fun t ht => le_antisymm ?_ (hx2 t)⟩
    exact (Valuation.map_sub _ _ _).trans (max_le hx1 (hT t ht))
  have fib_star : ∀ {x : K}, x ∈ affinoid ϖ 0 →
      (∀ t ∈ T, Valued.v (algebraMap K₀ K ϖ.ϖ) < Valued.v (x - algebraMap K₀ K t)) ∧
        Valued.v x < (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := fib hx
    exact ⟨fun t ht => by rw [hx2 t ht]; exact hp1, hx1.trans_lt hpinv⟩
  have prod_one : ∀ {x : K}, x ∈ affinoid ϖ 0 → ∀ k : K₀ → ℤ,
      ∏ t ∈ T, Valued.v (x - algebraMap K₀ K t) ^ (k t) = 1 := by
    intro x hx k
    refine Finset.prod_eq_one fun t ht => ?_
    rw [(fib hx).2 t ht, one_zpow]

  have h1 : Valued.v (F w') = c₀ := by
    rw [hstar w' (fib_star hw').1 (fib_star hw').2, prod_one hw', mul_one]
  have h2 : Valued.v (F (w * (algebraMap K₀ K ϖ.ϖ)⁻¹)) = c₀' := by
    rw [hstar' w (fib_star hw).1 (fib_star hw).2, prod_one hw, mul_one]
  rw [h1, h2]

  obtain ⟨t₀, ht₀T, ht₀⟩ := hTcov 0 (by simp)
  rw [map_zero, zero_sub, Valuation.map_neg] at ht₀
  have ht₀le : Valued.v (algebraMap K₀ K t₀) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) :=
    (hunif t₀).resolve_right (not_le.mpr ht₀)
  have hTother : ∀ t ∈ T, t ≠ t₀ → Valued.v (algebraMap K₀ K t) = 1 := by
    intro t ht hne
    refine le_antisymm (hT t ht) ?_
    have h := (hTsep t ht t₀ ht₀T hne).trans (Valuation.map_sub _ _ _)
    rcases le_max_iff.mp h with h | h
    · exact h
    · exact absurd h (not_le.mpr ht₀)

  have key : ∀ u : K, Valued.v (algebraMap K₀ K ϖ.ϖ) < Valued.v u → Valued.v u < 1 →
      c₀' * Valued.v u ^ (m' t₀) =
        (c₀ * Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (-(∑ t ∈ T, m t))) * Valued.v u ^ (∑ t ∈ T, m t) := by
    intro u hu1 hu2
    have hu0 : Valued.v u ≠ 0 := ne_of_gt (hp0.trans hu1)

    have hut : ∀ t ∈ T, Valued.v (u - algebraMap K₀ K t) = if t = t₀ then Valued.v u else 1 := by
      intro t ht
      split_ifs with h
      · subst h
        rw [sub_eq_add_neg, Valuation.map_add_eq_of_lt_left _ (by rw [Valuation.map_neg]; exact ht₀le.trans_lt hu1)]
      · rw [sub_eq_add_neg, Valuation.map_add_eq_of_lt_right _ (by rw [Valuation.map_neg, hTother t ht h]; exact hu2),
          Valuation.map_neg, hTother t ht h]

    have hA := hstar' u (fun t ht => by
        rw [hut t ht]; split_ifs
        · exact hu1
        · exact hp1) (hu2.trans hpinv)
    have hprodA : ∏ t ∈ T, Valued.v (u - algebraMap K₀ K t) ^ (m' t) = Valued.v u ^ (m' t₀) := by
      rw [← Finset.prod_erase_mul _ _ ht₀T, hut t₀ ht₀T, if_pos rfl]
      rw [Finset.prod_eq_one fun t ht => ?_, one_mul]
      rw [hut t (Finset.mem_of_mem_erase ht), if_neg (Finset.ne_of_mem_erase ht), one_zpow]
    rw [hprodA] at hA

    have hz : Valued.v (u * (algebraMap K₀ K ϖ.ϖ)⁻¹) = Valued.v u * (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ := by
      rw [map_mul, map_inv₀]
    have hz1 : 1 < Valued.v (u * (algebraMap K₀ K ϖ.ϖ)⁻¹) := by
      rw [hz]
      calc (1 : Γ₀) = Valued.v (algebraMap K₀ K ϖ.ϖ) * (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ := (mul_inv_cancel₀ hpne).symm
        _ < Valued.v u * (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ := mul_lt_mul_of_pos_right hu1 (inv_pos.mpr hp0)
    have hzt : ∀ t ∈ T, Valued.v (u * (algebraMap K₀ K ϖ.ϖ)⁻¹ - algebraMap K₀ K t) = Valued.v (u * (algebraMap K₀ K ϖ.ϖ)⁻¹) := by
      intro t ht
      rw [sub_eq_add_neg, Valuation.map_add_eq_of_lt_left _ ?_]
      rw [Valuation.map_neg]
      exact (hT t ht).trans_lt hz1
    have hzlt : Valued.v (u * (algebraMap K₀ K ϖ.ϖ)⁻¹) < (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ := by
      rw [hz]
      calc Valued.v u * (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹
          < 1 * (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ := mul_lt_mul_of_pos_right hu2 (inv_pos.mpr hp0)
        _ = (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ := one_mul _
    have hB := hstar (u * (algebraMap K₀ K ϖ.ϖ)⁻¹) (fun t ht => by rw [hzt t ht]; exact hp1.trans hz1) hzlt
    have hprodB : ∏ t ∈ T, Valued.v (u * (algebraMap K₀ K ϖ.ϖ)⁻¹ - algebraMap K₀ K t) ^ (m t) =
        (Valued.v u * (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹) ^ (∑ t ∈ T, m t) := by
      rw [← hz, ← hzsum _ ((Valuation.ne_zero_iff _).mpr ?_)]
      · exact Finset.prod_congr rfl fun t ht => by rw [hzt t ht]
      · exact mul_ne_zero ((Valuation.ne_zero_iff _).mp hu0) (inv_ne_zero hϖK)
    rw [hprodB, mul_zpow, inv_zpow', mul_comm (Valued.v u ^ _), ← mul_assoc] at hB
    rw [← hB, hA]

  obtain ⟨u₁, hu₁⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K₀ K ϖ.ϖ) (by norm_num : 0 < 2)
  obtain ⟨u₂, hu₂⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K₀ K ϖ.ϖ) (by norm_num : 0 < 3)
  have hv₁ : Valued.v u₁ ^ 2 = Valued.v (algebraMap K₀ K ϖ.ϖ) := by rw [← map_pow, hu₁]
  have hv₂ : Valued.v u₂ ^ 3 = Valued.v (algebraMap K₀ K ϖ.ϖ) := by rw [← map_pow, hu₂]
  have hu₁0 : Valued.v u₁ ≠ 0 := fun h => hpne (by rw [← hv₁, h, zero_pow two_ne_zero])
  have hu₂0 : Valued.v u₂ ≠ 0 := fun h => hpne (by rw [← hv₂, h, zero_pow three_ne_zero])
  have hu₁lt : Valued.v u₁ < 1 := by
    by_contra h
    exact absurd (hv₁ ▸ one_le_pow_of_one_le' (not_lt.mp h) 2) (not_le.mpr hp1)
  have hu₂lt : Valued.v u₂ < 1 := by
    by_contra h
    exact absurd (hv₂ ▸ one_le_pow_of_one_le' (not_lt.mp h) 3) (not_le.mpr hp1)
  have hu₁gt : Valued.v (algebraMap K₀ K ϖ.ϖ) < Valued.v u₁ := by
    rw [← hv₁, pow_two]
    exact mul_lt_of_lt_one_right (zero_lt_iff.mpr hu₁0) hu₁lt
  have hu₂gt : Valued.v (algebraMap K₀ K ϖ.ϖ) < Valued.v u₂ := by
    rw [← hv₂, pow_succ, pow_two]
    calc Valued.v u₂ * Valued.v u₂ * Valued.v u₂ < Valued.v u₂ * Valued.v u₂ :=
          mul_lt_of_lt_one_right (mul_pos (zero_lt_iff.mpr hu₂0) (zero_lt_iff.mpr hu₂0)) hu₂lt
      _ < Valued.v u₂ := mul_lt_of_lt_one_right (zero_lt_iff.mpr hu₂0) hu₂lt
  have hne : Valued.v u₁ ≠ Valued.v u₂ := by
    intro h
    have : Valued.v u₂ ^ 2 * 1 = Valued.v u₂ ^ 2 * Valued.v u₂ := by
      rw [mul_one, ← pow_succ, hv₂, ← hv₁, h]
    exact absurd (mul_left_cancel₀ (pow_ne_zero 2 hu₂0) this).symm (ne_of_lt hu₂lt)
  have k₁ := key u₁ hu₁gt hu₁lt
  have k₂ := key u₂ hu₂gt hu₂lt
  rcases eq_or_ne c₀ 0 with h0 | h0
  · rw [h0, zero_mul] at k₁ ⊢
    rw [zero_mul] at k₁
    exact (mul_eq_zero.mp k₁).resolve_right (zpow_ne_zero _ hu₁0)
  · exact UAPEdge.eq_of_two_radii (mul_ne_zero h0 (zpow_ne_zero _ hpne)) hu₁0 hu₂0 hne k₁ k₂

end S_CerednikDrinfeld_Omega_v_apply_mul_inv_eq_mul_zpow_neg_sum_of_star
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_v_apply_mul_inv_eq_mul_zpow_neg_sum_of_star (solution)
