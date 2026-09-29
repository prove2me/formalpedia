-- Prove2me | solution 1 for CerednikDrinfeld.Omega.affinoid_nonempty_of_exists_finset_cover
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/71b38266-e6aa-58cc-a154-84b0ac666817

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_affinoid_nonempty_of_exists_finset_cover

set_option autoImplicit false

open CerednikDrinfeld.Omega

namespace NONTRIV

theorem exists_v_le_one_forall_v_sub_eq_one {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] [IsAlgClosed K] (S : Finset K) (hS : ∀ s ∈ S, Valued.v s ≤ 1) :
    ∃ y : K, Valued.v y ≤ 1 ∧ ∀ s ∈ S, Valued.v (y - s) = 1 := by
  classical
  by_cases hS0 : S = ∅
  · exact ⟨0, by rw [Valuation.map_zero]; exact zero_le', by simp [hS0]⟩
  have hcard : S.card ≠ 0 := by rwa [ne_eq, Finset.card_eq_zero]
  set Q : Polynomial K := (∏ s ∈ S, (Polynomial.X - Polynomial.C s)) + 1 with hQ
  have hmonic : (∏ s ∈ S, (Polynomial.X - Polynomial.C s)).Monic :=
    Polynomial.monic_prod_of_monic _ _ fun s _ => Polynomial.monic_X_sub_C s
  have hdegP : (∏ s ∈ S, (Polynomial.X - Polynomial.C s)).natDegree = S.card := by
    rw [Polynomial.natDegree_prod_of_monic _ _ fun s _ => Polynomial.monic_X_sub_C s]
    simp
  have hQdeg : Q.degree ≠ 0 := by
    have hQmonic : Q.Monic := hmonic.add_of_left (by
      rw [Polynomial.degree_one]
      rw [Polynomial.degree_eq_natDegree hmonic.ne_zero, hdegP]
      exact_mod_cast Nat.pos_of_ne_zero hcard)
    rw [Polynomial.degree_eq_natDegree hQmonic.ne_zero]
    have : Q.natDegree = S.card := by
      rw [hQ, Polynomial.natDegree_add_eq_left_of_degree_lt, hdegP]
      rw [Polynomial.degree_one, Polynomial.degree_eq_natDegree hmonic.ne_zero, hdegP]
      exact_mod_cast Nat.pos_of_ne_zero hcard
    rw [this]
    exact_mod_cast hcard
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root Q hQdeg
  have hprod : ∏ s ∈ S, (y - s) = -1 := by
    have : Polynomial.eval y Q = 0 := hy
    rw [hQ, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_prod] at this
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at this
    exact eq_neg_of_add_eq_zero_left this
  have hvprod : ∏ s ∈ S, Valued.v (y - s) = 1 := by
    rw [← map_prod (Valued.v : Valuation K Γ₀), hprod, Valuation.map_neg, Valuation.map_one]

  have hy1 : Valued.v y ≤ 1 := by
    by_contra hlt
    push Not at hlt
    have heach : ∀ s ∈ S, Valued.v (y - s) = Valued.v y := by
      intro s hs
      rw [sub_eq_add_neg, Valuation.map_add_eq_of_lt_left]
      rw [Valuation.map_neg]
      exact (hS s hs).trans_lt hlt
    rw [Finset.prod_congr rfl heach, Finset.prod_const] at hvprod
    exact (one_lt_pow₀ hlt hcard).ne' hvprod
  refine ⟨y, hy1, fun s₀ hs₀ => ?_⟩

  have hle : ∀ s ∈ S, Valued.v (y - s) ≤ 1 := fun s hs =>
    (Valuation.map_sub _ _ _).trans (max_le hy1 (hS s hs))
  by_contra hne
  have hlt : Valued.v (y - s₀) < 1 := lt_of_le_of_ne (hle s₀ hs₀) hne
  have : ∏ s ∈ S, Valued.v (y - s) < 1 := by
    rw [← Finset.mul_prod_erase S _ hs₀]
    calc Valued.v (y - s₀) * ∏ s ∈ S.erase s₀, Valued.v (y - s) ≤ Valued.v (y - s₀) * 1 := by
          gcongr
          exact Finset.prod_le_one' fun s hs => hle s (Finset.mem_of_mem_erase hs)
      _ < 1 := by rw [mul_one]; exact hlt
  exact this.ne hvprod

end NONTRIV

theorem solution
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K) (n : ℕ)
    (hfin : ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n) :
    (affinoid ϖ n).Nonempty := by
  classical
  obtain ⟨T, hT⟩ := hfin
  set p := Valued.v (algebraMap K₀ K ϖ.ϖ) with hp
  have hp0 : 0 < p := ϖ.pos
  have hp1 : p ≤ 1 := ϖ.lt_one.le
  have hpn1 : p ^ n ≤ 1 := pow_le_one₀ zero_le' hp1
  have hpinv : (1 : Γ₀) ≤ p⁻¹ ^ n := one_le_pow₀ ((one_le_inv₀ hp0).2 hp1)

  obtain ⟨z, hz1, hzS⟩ := NONTRIV.exists_v_le_one_forall_v_sub_eq_one
    ((T.filter fun t => Valued.v (algebraMap K₀ K t) ≤ 1).image (algebraMap K₀ K))
    (by
      intro s hs
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
      exact (Finset.mem_filter.mp ht).2)

  have hzt : ∀ t ∈ T, 1 ≤ Valued.v (z - algebraMap K₀ K t) := by
    intro t ht
    by_cases h1 : Valued.v (algebraMap K₀ K t) ≤ 1
    · exact (hzS _ (Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨ht, h1⟩, rfl⟩)).ge
    · push Not at h1
      rw [sub_eq_add_neg, Valuation.map_add_eq_of_lt_right, Valuation.map_neg]
      · exact h1.le
      · rw [Valuation.map_neg]; exact hz1.trans_lt h1
  refine ⟨z, hz1.trans hpinv, fun a ha => ?_⟩
  obtain ⟨t, ht, hat⟩ := hT a ha

  have hlt : Valued.v (algebraMap K₀ K t - algebraMap K₀ K a) < Valued.v (z - algebraMap K₀ K t) := by
    rw [← Valuation.map_neg, neg_sub] at hat
    rw [← neg_sub, Valuation.map_neg]
    rw [← neg_sub, Valuation.map_neg] at hat
    exact hat.trans_le (hpn1.trans (hzt t ht))
  have heq : z - algebraMap K₀ K a = (z - algebraMap K₀ K t) + (algebraMap K₀ K t - algebraMap K₀ K a) := by ring
  rw [heq, Valuation.map_add_eq_of_lt_left _ hlt]
  exact hpn1.trans (hzt t ht)

end S_CerednikDrinfeld_Omega_affinoid_nonempty_of_exists_finset_cover
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_affinoid_nonempty_of_exists_finset_cover (solution)
