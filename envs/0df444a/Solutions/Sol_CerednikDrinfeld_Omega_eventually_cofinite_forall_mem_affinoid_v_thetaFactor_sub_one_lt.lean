-- Prove2me | solution 1 for CerednikDrinfeld.Omega.eventually_cofinite_forall_mem_affinoid_v_thetaFactor_sub_one_lt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/3c4782a5-2d93-5878-9f32-badc3bfe5955

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import Theorems.Thm_CerednikDrinfeld_Omega_crossRatio_pmoebius_pmoebius_sub_one_eq
import Theorems.Thm_CerednikDrinfeld_Omega_pow_le_v_phi_of_mem_affinoid_of_v_det_lt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_eventually_cofinite_forall_mem_affinoid_v_thetaFactor_sub_one_lt

set_option autoImplicit false

open scoped MatrixGroups
open Filter CerednikDrinfeld.Omega

namespace Law2T2B

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

end Law2T2B

theorem solution
    {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (ϖ : PseudoUniformizer K₀ K) {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ)
    (n : ℕ) {a b z₀ : K} (ha : a ∈ affinoid ϖ n) (hb : b ∈ affinoid ϖ n) (hz₀ : z₀ ∈ affinoid ϖ n)
    (ε : Γ₀) (hε : ε ≠ 0) :
    ∀ᶠ γ in cofinite, ∀ z ∈ affinoid ϖ n, Valued.v (thetaFactor ρ a b z₀ z γ - 1) < ε := by
  classical
  set q : Γ₀ := Valued.v (algebraMap K₀ K ϖ.ϖ) with hq
  have hq0 : q ≠ 0 := ϖ.pos.ne'
  have hqn : ∀ k : ℕ, q ^ k ≠ 0 := fun k => pow_ne_zero k hq0
  have hqpos : ∀ k : ℕ, 0 < q ^ k := fun k => zero_lt_iff.2 (hqn k)
  set η : Γ₀ := min (q ^ (6 * n)) (ε * q ^ (10 * n)) with hη
  have hη0 : η ≠ 0 := (lt_min (hqpos _) (mul_pos (zero_lt_iff.2 hε) (hqpos _))).ne'
  have haΩ : a ∈ upperHalfPlane K₀ K := affinoid_subset_upperHalfPlane ϖ n ha
  have hbΩ : b ∈ upperHalfPlane K₀ K := affinoid_subset_upperHalfPlane ϖ n hb
  rw [Filter.eventually_cofinite]
  refine (hρ η hη0).subset ?_
  intro γ hγ
  simp only [Set.mem_setOf_eq, not_forall, exists_prop] at hγ
  obtain ⟨z, hz, hbad⟩ := hγ
  simp only [Set.mem_setOf_eq]
  obtain ⟨g₀, hg₀⟩ := Matrix.ProjGenLinGroup.mk_surjective (ρ γ)
  obtain ⟨g, hg, hle, hone⟩ := Law2T2B.exists_normalised (K := K) g₀
  refine ⟨g, hg.trans hg₀, hle, ?_⟩
  by_contra hlt
  push_neg at hlt
  apply hbad
  have hdet6 : Valued.v (algebraMap K₀ K (Matrix.det (g : Matrix (Fin 2) (Fin 2) K₀))) < q ^ (6 * n) :=
    hlt.trans_le (min_le_left _ _)
  have hdetε : Valued.v (algebraMap K₀ K (Matrix.det (g : Matrix (Fin 2) (Fin 2) K₀))) < ε * q ^ (10 * n) :=
    hlt.trans_le (min_le_right _ _)
  have hΦ := CerednikDrinfeld.Omega.pow_le_v_phi_of_mem_affinoid_of_v_det_lt ϖ n hb hz
    (g : Matrix (Fin 2) (Fin 2) K₀) hle hone hdet6
  have hΦ₀ := CerednikDrinfeld.Omega.pow_le_v_phi_of_mem_affinoid_of_v_det_lt ϖ n ha hz₀
    (g : Matrix (Fin 2) (Fin 2) K₀) hle hone hdet6
  have hΦpos := (hqpos (4 * n)).trans_le hΦ
  have hΦ₀pos := (hqpos (4 * n)).trans_le hΦ₀
  have hΦne := (Valuation.pos_iff _).1 hΦpos
  have hΦ₀ne := (Valuation.pos_iff _).1 hΦ₀pos
  have hid := CerednikDrinfeld.Omega.crossRatio_pmoebius_pmoebius_sub_one_eq g z z₀ haΩ hbΩ hΦne hΦ₀ne
  have hF : thetaFactor ρ a b z₀ z γ =
      crossRatio z z₀ (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g) a) (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g) b) := by
    rw [hg, hg₀]; rfl
  rw [hF, hid, map_div₀, Valuation.map_mul, Valuation.map_mul, Valuation.map_mul, div_lt_iff₀ (mul_pos hΦpos hΦ₀pos)]
  have hzz := Law2T2B.v_sub_le ϖ n hz hz₀
  have hab := Law2T2B.v_sub_le ϖ n ha hb
  have hcancel : q⁻¹ ^ n * q ^ n = 1 := by rw [inv_pow, inv_mul_cancel₀ (hqn n)]
  calc Valued.v (z - z₀) * Valued.v (a - b) * Valued.v (algebraMap K₀ K (Matrix.det (g : Matrix (Fin 2) (Fin 2) K₀)))
      ≤ q⁻¹ ^ n * q⁻¹ ^ n * Valued.v (algebraMap K₀ K (Matrix.det (g : Matrix (Fin 2) (Fin 2) K₀))) :=
        mul_le_mul_left (mul_le_mul' hzz hab) _
    _ < q⁻¹ ^ n * q⁻¹ ^ n * (ε * q ^ (10 * n)) :=
        mul_lt_mul_of_pos_left hdetε (mul_pos (pow_pos (inv_pos.2 (zero_lt_iff.2 hq0)) n)
          (pow_pos (inv_pos.2 (zero_lt_iff.2 hq0)) n))
    _ = ε * (q ^ (4 * n) * q ^ (4 * n)) := by
        rw [show 10 * n = n + n + (4 * n + 4 * n) by ring, pow_add, pow_add, pow_add]
        calc q⁻¹ ^ n * q⁻¹ ^ n * (ε * (q ^ n * q ^ n * (q ^ (4 * n) * q ^ (4 * n))))
            = (q⁻¹ ^ n * q ^ n) * (q⁻¹ ^ n * q ^ n) * (ε * (q ^ (4 * n) * q ^ (4 * n))) := by ac_rfl
          _ = ε * (q ^ (4 * n) * q ^ (4 * n)) := by rw [hcancel, one_mul, one_mul]
    _ ≤ ε * (Valued.v (z * (algebraMap K₀ K (g 1 0) * b + algebraMap K₀ K (g 1 1)) - (algebraMap K₀ K (g 0 0) * b + algebraMap K₀ K (g 0 1))) *
          Valued.v (z₀ * (algebraMap K₀ K (g 1 0) * a + algebraMap K₀ K (g 1 1)) - (algebraMap K₀ K (g 0 0) * a + algebraMap K₀ K (g 0 1)))) :=
        mul_le_mul_right (mul_le_mul' hΦ hΦ₀) ε

end S_CerednikDrinfeld_Omega_eventually_cofinite_forall_mem_affinoid_v_thetaFactor_sub_one_lt
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_eventually_cofinite_forall_mem_affinoid_v_thetaFactor_sub_one_lt (solution)
