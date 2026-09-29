-- Prove2me | solution 1 for CerednikDrinfeld.Omega.finite_setOf_pmoebius_mem_affinoid
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/d487f949-bef4-5f28-bd50-ff07037eb058

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import Theorems.Thm_CerednikDrinfeld_Omega_pow_le_v_phi_of_mem_affinoid_of_v_det_lt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_finite_setOf_pmoebius_mem_affinoid

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

namespace Law2Orb

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
  {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

theorem v_sub_le (ϖ : PseudoUniformizer K₀ K) (n : ℕ) {x y : K} (hx : x ∈ affinoid ϖ n) (hy : y ∈ affinoid ϖ n) :
    Valued.v (x - y) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n :=
  (Valuation.map_sub _ x y).trans (max_le ((mem_affinoid_iff' ϖ n x).1 hx).1 ((mem_affinoid_iff' ϖ n y).1 hy).1)

theorem exists_normalised (g₀ : GL (Fin 2) K₀) :
    ∃ g : GL (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g = Matrix.ProjGenLinGroup.mk g₀ ∧
      (∀ i j : Fin 2, Valued.v (algebraMap K₀ K (g i j)) ≤ 1) ∧
      ∃ i j : Fin 2, Valued.v (algebraMap K₀ K (g i j)) = 1 := by
  classical
  obtain ⟨p, -, hp⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 2 × Fin 2))
    (fun p => Valued.v (algebraMap K₀ K (g₀ p.1 p.2))) Finset.univ_nonempty
  set m : K₀ := g₀ p.1 p.2 with hm_def
  have hm : m ≠ 0 := by
    intro hm0
    apply g₀.det_ne_zero
    have hall : ∀ i j : Fin 2, g₀ i j = 0 := by
      intro i j
      have h := hp (i, j) (Finset.mem_univ _)
      rw [hm0, map_zero, Valuation.map_zero, le_zero_iff, Valuation.zero_iff] at h
      exact (algebraMap K₀ K).injective (by rw [h, map_zero])
    rw [Matrix.det_fin_two]
    simp [hall]
  refine ⟨g₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 m hm)⁻¹, ?_, ?_, ?_⟩
  · rw [map_mul, Matrix.ProjGenLinGroup.mk_scalar, mul_one]
  · have hentry : ∀ i j : Fin 2, (g₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 m hm)⁻¹) i j = g₀ i j * m⁻¹ := by
      intro i j
      simp [Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Matrix.diagonal_apply]
    have hvm : Valued.v (algebraMap K₀ K m) ≠ 0 := by
      rw [ne_eq, Valuation.zero_iff]; exact fun h => hm ((algebraMap K₀ K).injective (by rw [h, map_zero]))
    intro i j
    rw [hentry, map_mul, map_inv₀, Valuation.map_mul, Valuation.map_inv, mul_inv_le_iff₀ (zero_lt_iff.2 hvm),
      one_mul]
    exact hp (i, j) (Finset.mem_univ _)
  · refine ⟨p.1, p.2, ?_⟩
    have hentry : (g₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 m hm)⁻¹) p.1 p.2 = g₀ p.1 p.2 * m⁻¹ := by
      simp [Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Matrix.diagonal_apply]
    rw [hentry, ← hm_def, mul_inv_cancel₀ hm, map_one, Valuation.map_one]

end Law2Orb

theorem solution
    {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (ϖ : PseudoUniformizer K₀ K) {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ)
    (n : ℕ) {b : K} (hb : b ∈ affinoid ϖ n) :
    {γ : G | pmoebius K₀ (ρ γ) b ∈ affinoid ϖ n}.Finite := by
  classical
  set q : Γ₀ := Valued.v (algebraMap K₀ K ϖ.ϖ) with hq
  have hq0 : q ≠ 0 := ϖ.pos.ne'
  have hqn : ∀ k : ℕ, q ^ k ≠ 0 := fun k => pow_ne_zero k hq0
  refine (hρ (q ^ (6 * n)) (hqn _)).subset ?_
  intro γ hγ
  simp only [Set.mem_setOf_eq] at hγ ⊢
  have hbΩ : b ∈ upperHalfPlane K₀ K := affinoid_subset_upperHalfPlane ϖ n hb
  obtain ⟨g₀, hg₀⟩ := Matrix.ProjGenLinGroup.mk_surjective (ρ γ)
  obtain ⟨g, hg, hle, hone⟩ := Law2Orb.exists_normalised (K := K) g₀
  refine ⟨g, hg.trans hg₀, hle, ?_⟩
  by_contra hlt
  push_neg at hlt
  set z : K := pmoebius K₀ (ρ γ) b with hz_def
  have hΦ := CerednikDrinfeld.Omega.pow_le_v_phi_of_mem_affinoid_of_v_det_lt ϖ n hb hγ
    (g : Matrix (Fin 2) (Fin 2) K₀) hle hone hlt
  have hcb := moebius_denom_ne_zero_of_mem K₀ hbΩ g
  have hzero : pmoebius K₀ (ρ γ) b * (algebraMap K₀ K (g 1 0) * b + algebraMap K₀ K (g 1 1)) -
      (algebraMap K₀ K (g 0 0) * b + algebraMap K₀ K (g 0 1)) = 0 := by
    rw [← hg₀, ← hg, pmoebius_mk K₀ g b hcb, moebius, div_mul_cancel₀ _ hcb, sub_self]
  rw [hzero, Valuation.map_zero, le_zero_iff] at hΦ
  exact hqn _ hΦ

end S_CerednikDrinfeld_Omega_finite_setOf_pmoebius_mem_affinoid
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_finite_setOf_pmoebius_mem_affinoid (solution)
