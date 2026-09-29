-- Prove2me | solution 1 for CerednikDrinfeld.Omega.exists_pmoebius_inv_mem_affinoid_zero_or_v_lt_lt_one_of_isExhausted
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/290a4f96-3c62-58ab-825d-edd37f36a6d0

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_exists_pmoebius_inv_mem_affinoid_zero_or_v_lt_lt_one_of_isExhausted

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem solution
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (ϖ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ)

    (hval : ∀ a : K₀, a ≠ 0 → ∃ k : ℤ, Valued.v (algebraMap K₀ K a) = Valued.v (algebraMap K₀ K ϖ.ϖ) ^ k)
    {z : K} (hz : z ∈ upperHalfPlane K₀ K) :
    ∃ g : PGL(2, K₀),
      pmoebius K₀ g⁻¹ z ∈ affinoid ϖ 0 ∨
      (Valued.v (algebraMap K₀ K ϖ.ϖ) < Valued.v (pmoebius K₀ g⁻¹ z) ∧ Valued.v (pmoebius K₀ g⁻¹ z) < 1) := by
  classical
  set q : Γ₀ := Valued.v (algebraMap K₀ K ϖ.ϖ) with hq
  have hq0 : 0 < q := ϖ.pos
  have hq0' : q ≠ 0 := hq0.ne'
  have hq1 : q < 1 := ϖ.lt_one
  have hϖ0 : ϖ.ϖ ≠ 0 := fun h => hq0' (by rw [hq, h, map_zero, map_zero])
  have hanti := zpow_right_strictAnti₀ hq0 hq1

  have hzK : ∀ a : K₀, z - algebraMap K₀ K a ≠ 0 := fun a h =>
    ((mem_upperHalfPlane_iff K₀ z).1 hz) a (sub_eq_zero.1 h).symm
  have hD0 : ∀ a : K₀, Valued.v (z - algebraMap K₀ K a) ≠ 0 := fun a => (Valuation.ne_zero_iff _).2 (hzK a)

  obtain ⟨n, hn⟩ := hex z hz
  obtain ⟨hz1, hz2⟩ := (mem_affinoid_iff' ϖ n z).1 hn

  obtain ⟨a₀, hmin⟩ : ∃ a₀ : K₀, ∀ a : K₀, Valued.v (z - algebraMap K₀ K a₀) ≤ Valued.v (z - algebraMap K₀ K a) := by
    by_cases hA : ∃ a₀ : K₀, ∀ k : ℤ, Valued.v (z - algebraMap K₀ K a₀) ≠ q ^ k
    ·
      obtain ⟨a₀, ha₀⟩ := hA
      refine ⟨a₀, fun a => ?_⟩
      by_cases haa : a = a₀
      · rw [haa]
      have hne : Valued.v (algebraMap K₀ K a - algebraMap K₀ K a₀) ≠ Valued.v (z - algebraMap K₀ K a₀) := by
        obtain ⟨k, hk⟩ := hval (a - a₀) (sub_ne_zero.2 haa)
        rw [← map_sub, hk]; exact (ha₀ k).symm
      have e : z - algebraMap K₀ K a = (z - algebraMap K₀ K a₀) - (algebraMap K₀ K a - algebraMap K₀ K a₀) := by ring
      rcases lt_or_gt_of_ne hne with h | h
      · rw [e, Valuation.map_sub_eq_of_lt_left _ h]
      · rw [e, Valuation.map_sub_eq_of_lt_right _ h]; exact h.le
    ·
      push_neg at hA
      choose e he using hA
      have hbd : ∀ a : K₀, e a ≤ n := by
        intro a
        have := hz2 a
        rw [he a, ← zpow_natCast] at this
        exact (hanti.le_iff_ge).1 this
      obtain ⟨k₀, ⟨a₀, rfl⟩, hk₀⟩ := Int.exists_greatest_of_bdd (P := fun k => ∃ a : K₀, e a = k)
        ⟨n, fun k ⟨a, ha⟩ => ha ▸ hbd a⟩ ⟨e 0, 0, rfl⟩
      refine ⟨a₀, fun a => ?_⟩
      rw [he a₀, he a]
      exact hanti.antitone (hk₀ (e a) ⟨a, rfl⟩)
  set m : Γ₀ := Valued.v (z - algebraMap K₀ K a₀) with hm
  have hm0 : m ≠ 0 := hD0 a₀

  have hmat : ∀ k : ℤ, ∃ g : PGL(2, K₀), pmoebius K₀ g⁻¹ z = (z - algebraMap K₀ K a₀) * (algebraMap K₀ K ϖ.ϖ ^ k)⁻¹ := by
    intro k
    let A : Matrix (Fin 2) (Fin 2) K₀ := !![(ϖ.ϖ ^ k)⁻¹, -(a₀ * (ϖ.ϖ ^ k)⁻¹); 0, 1]
    have hdet : A.det ≠ 0 := by
      simp [A, Matrix.det_fin_two, zpow_ne_zero k hϖ0]
    refine ⟨(Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.mkOfDetNeZero A hdet))⁻¹, ?_⟩
    rw [inv_inv, pmoebius_mk K₀ _ z (by simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, A]), moebius]
    simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, A, map_zpow₀]
    ring

  by_cases hpow : ∃ k : ℤ, m = q ^ k
  · obtain ⟨k, hk⟩ := hpow
    obtain ⟨g, hg⟩ := hmat k
    refine ⟨g, Or.inl ?_⟩
    rw [hg, mem_affinoid_iff']
    simp only [pow_zero]
    have hvw : Valued.v ((z - algebraMap K₀ K a₀) * (algebraMap K₀ K ϖ.ϖ ^ k)⁻¹) = 1 := by
      rw [Valuation.map_mul, Valuation.map_inv, map_zpow₀, ← hq, ← hm, hk, mul_inv_cancel₀ (zpow_ne_zero k hq0')]
    refine ⟨hvw.le, fun t => ?_⟩
    have e : (z - algebraMap K₀ K a₀) * (algebraMap K₀ K ϖ.ϖ ^ k)⁻¹ - algebraMap K₀ K t =
        (z - algebraMap K₀ K (a₀ + ϖ.ϖ ^ k * t)) * (algebraMap K₀ K ϖ.ϖ ^ k)⁻¹ := by
      have hϖK : algebraMap K₀ K ϖ.ϖ ^ k ≠ 0 := zpow_ne_zero k ((Valuation.ne_zero_iff Valued.v).1 hq0')
      rw [map_add, map_mul, map_zpow₀]; field_simp; ring
    rw [e, Valuation.map_mul, Valuation.map_inv, map_zpow₀, ← hq]
    calc (1 : Γ₀) = m * (q ^ k)⁻¹ := by rw [hk, mul_inv_cancel₀ (zpow_ne_zero k hq0')]
      _ ≤ Valued.v (z - algebraMap K₀ K (a₀ + ϖ.ϖ ^ k * t)) * (q ^ k)⁻¹ :=
          mul_le_mul_left (hmin _) _
  · push_neg at hpow

    have hup : m < q ^ (-(n : ℤ) - 1) := by
      have hva₀ : Valued.v (algebraMap K₀ K a₀) ≤ q⁻¹ ^ n := by
        by_contra hgt
        push_neg at hgt
        have ha0 : a₀ ≠ 0 := fun h0 => by rw [h0, map_zero, Valuation.map_zero] at hgt; exact not_lt_zero hgt
        obtain ⟨j, hj⟩ := hval a₀ ha0
        apply hpow j
        rw [hm, sub_eq_add_neg, Valuation.map_add_eq_of_lt_right _ (by rw [Valuation.map_neg]; exact hz1.trans_lt hgt),
          Valuation.map_neg, hj]
      calc m ≤ max (Valued.v z) (Valued.v (algebraMap K₀ K a₀)) := Valuation.map_sub _ _ _
        _ ≤ q⁻¹ ^ n := max_le hz1 hva₀
        _ = q ^ (-(n : ℤ)) := by rw [zpow_neg, zpow_natCast, inv_pow]
        _ < q ^ (-(n : ℤ) - 1) := hanti (by linarith)
    obtain ⟨k, hk, hkmax⟩ := Int.exists_greatest_of_bdd (P := fun k => m < q ^ k)
      ⟨n, fun k hk => by
        by_contra hlt; push_neg at hlt
        have h1 : q ^ k < q ^ (n : ℤ) := hanti hlt
        rw [zpow_natCast] at h1
        exact absurd ((hz2 a₀).trans_lt (hk.trans h1)) (lt_irrefl _)⟩ ⟨-(n : ℤ) - 1, hup⟩
    have hlow : q ^ (k + 1) < m := by
      rcases lt_or_ge (q ^ (k + 1)) m with h | h
      · exact h
      · exact absurd (hkmax (k + 1) (lt_of_le_of_ne h (hpow (k + 1)))) (by linarith)
    obtain ⟨g, hg⟩ := hmat k
    refine ⟨g, Or.inr ?_⟩
    rw [hg, Valuation.map_mul, Valuation.map_inv, map_zpow₀, ← hq, ← hm]
    constructor
    · calc q = q ^ (k + 1) * (q ^ k)⁻¹ := by rw [zpow_add_one₀ hq0', mul_comm, ← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero k hq0'), one_mul]
        _ < m * (q ^ k)⁻¹ := mul_lt_mul_of_pos_right hlow (inv_pos.2 (zpow_pos hq0 k))
    · calc m * (q ^ k)⁻¹ < q ^ k * (q ^ k)⁻¹ := mul_lt_mul_of_pos_right hk (inv_pos.2 (zpow_pos hq0 k))
        _ = 1 := mul_inv_cancel₀ (zpow_ne_zero k hq0')

end S_CerednikDrinfeld_Omega_exists_pmoebius_inv_mem_affinoid_zero_or_v_lt_lt_one_of_isExhausted
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_exists_pmoebius_inv_mem_affinoid_zero_or_v_lt_lt_one_of_isExhausted (solution)
