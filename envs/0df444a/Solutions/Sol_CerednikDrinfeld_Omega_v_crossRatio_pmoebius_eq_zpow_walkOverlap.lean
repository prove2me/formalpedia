-- Prove2me | solution 1 for CerednikDrinfeld.Omega.v_crossRatio_pmoebius_eq_zpow_walkOverlap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/cd884113-a5b9-51a0-8bfb-99bacb8451bd

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_WalkOverlap
import Definitions.Def_LatticeTreeBaseChange
import Theorems.Thm_CerednikDrinfeld_Omega_crossRatio_pmoebius_eq_div_symp
import Theorems.Thm_CerednikDrinfeld_Omega_v_phi_eq_one_of_mem_affinoid_zero_of_v_det_lt_one
import Theorems.Thm_CerednikDrinfeld_BruhatTits_dist_stdVertex_smul_stdVertex_eq_of_isInteger_of_det_eq_of_isUnit
import Theorems.Thm_CerednikDrinfeld_Mumford_GraphAction_dist_smul_smul
import Theorems.Thm_CerednikDrinfeld_Mumford_dist_add_dist_sub_dist_sub_dist_eq_two_mul_walkOverlap
import Theorems.Thm_CerednikDrinfeld_BruhatTits_tree_isTree
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Tactic.FieldSimp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_v_crossRatio_pmoebius_eq_zpow_walkOverlap
p2m_attr_erase "simp" "LocalGL2.swapUnit_val"

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

namespace Law3CRV

noncomputable def S {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
    (w u : K) (h : Matrix (Fin 2) (Fin 2) K₀) : K :=
  w * (algebraMap K₀ K (h 1 0) * u + algebraMap K₀ K (h 1 1)) - (algebraMap K₀ K (h 0 0) * u + algebraMap K₀ K (h 0 1))

theorem exists_normalised {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] (g₀ : GL (Fin 2) K₀) :
    ∃ (c : K₀) (hc : c ≠ 0) (i₀ j₀ : Fin 2),
      (∀ i j : Fin 2, Valued.v (algebraMap K₀ K ((g₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 c hc)⁻¹) i j)) ≤ 1) ∧
      (g₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 c hc)⁻¹) i₀ j₀ = 1 ∧
      (∀ i j : Fin 2, (g₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 c hc)⁻¹) i j = g₀ i j * c⁻¹) := by
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
  have hentry : ∀ i j : Fin 2, (g₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 m hm)⁻¹) i j = g₀ i j * m⁻¹ := by
    intro i j
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Matrix.diagonal_apply]
  refine ⟨m, hm, p.1, p.2, ?_, ?_, hentry⟩
  · have hvm : Valued.v (algebraMap K₀ K m) ≠ 0 := by
      rw [ne_eq, Valuation.zero_iff]; exact fun h => hm ((algebraMap K₀ K).injective (by rw [h, map_zero]))
    intro i j
    rw [hentry, map_mul, map_inv₀, Valuation.map_mul, Valuation.map_inv, mul_inv_le_iff₀ (zero_lt_iff.2 hvm),
      one_mul]
    exact hp (i, j) (Finset.mem_univ _)
  · rw [hentry, ← hm_def, mul_inv_cancel₀ hm]

theorem key
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ)
    (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (ϖ₁ : PseudoUniformizer K₀ K) {w u : K} (hw : w ∈ affinoid ϖ₁ 0) (hu : u ∈ affinoid ϖ₁ 0)
    (h : GL (Fin 2) K₀) (hne : h • LT.LatticeTree.stdVertex R K₀ ≠ LT.LatticeTree.stdVertex R K₀) :
    S w u (h : Matrix (Fin 2) (Fin 2) K₀) ≠ 0 ∧
      Valued.v (S w u (h : Matrix (Fin 2) (Fin 2) K₀)) ^ 2 *
          Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^
            ((CerednikDrinfeld.BruhatTits.tree R K₀).dist (LT.LatticeTree.stdVertex R K₀)
              (h • LT.LatticeTree.stdVertex R K₀)) =
        Valued.v (algebraMap K₀ K (Matrix.det (h : Matrix (Fin 2) (Fin 2) K₀))) := by
  classical
  have hinjK : Function.Injective (algebraMap K₀ K) := (algebraMap K₀ K).injective
  have hinjR : Function.Injective (algebraMap R K₀) := IsFractionRing.injective R K₀
  set q : Γ₀ := Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) with hq_def
  have hq0 : q ≠ 0 := by
    rw [hq_def, ne_eq, Valuation.zero_iff, map_eq_zero_iff _ hinjK, map_eq_zero_iff _ hinjR]
    exact hϖ.ne_zero
  have hq1 : q < 1 := by
    refine lt_of_le_of_ne (hint ϖ) ?_
    intro h1
    apply hϖ.not_isUnit
    have hinv : Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)⁻¹) ≤ 1 := by
      rw [map_inv₀, Valuation.map_inv, ← hq_def, h1, inv_one]
    obtain ⟨a, ha⟩ := hv _ hinv
    have hϖ0 : algebraMap R K₀ ϖ ≠ 0 := fun h => hϖ.ne_zero (hinjR (by rw [h, map_zero]))
    have hmul : a * ϖ = 1 := hinjR (by rw [map_mul, ha, map_one, inv_mul_cancel₀ hϖ0])
    exact ⟨⟨ϖ, a, (mul_comm ϖ a).trans hmul, hmul⟩, rfl⟩
  have hunit : ∀ x : Rˣ, Valued.v (algebraMap K₀ K (algebraMap R K₀ (x : R))) = 1 := by
    intro x
    apply le_antisymm (hint x)
    have h' := hint (x⁻¹ : Rˣ)
    have hprod : Valued.v (algebraMap K₀ K (algebraMap R K₀ (x : R))) *
        Valued.v (algebraMap K₀ K (algebraMap R K₀ ((x⁻¹ : Rˣ) : R))) = 1 := by
      rw [← Valuation.map_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, Valuation.map_one]
    calc (1 : Γ₀) = _ := hprod.symm
      _ ≤ Valued.v (algebraMap K₀ K (algebraMap R K₀ (x : R))) * 1 := mul_le_mul_right h' _
      _ = _ := mul_one _

  obtain ⟨c, hc, i₀, j₀, hle, hone, hentry⟩ := exists_normalised (K := K) h
  set m : GL (Fin 2) K₀ := h * Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 c hc)⁻¹ with hm_def
  have hmv : m • LT.LatticeTree.stdVertex R K₀ = h • LT.LatticeTree.stdVertex R K₀ := by
    rw [hm_def, mul_smul, CerednikDrinfeld.BruhatTits.scalar_smul_vertex]
  have e : ∀ i j : Fin 2, (h : Matrix (Fin 2) (Fin 2) K₀) i j = (m : Matrix (Fin 2) (Fin 2) K₀) i j * c := by
    intro i j
    show h i j = m i j * c
    rw [hentry i j, inv_mul_cancel_right₀ hc]
  have hS : S w u (h : Matrix (Fin 2) (Fin 2) K₀) = algebraMap K₀ K c * S w u (m : Matrix (Fin 2) (Fin 2) K₀) := by
    simp only [S, e, map_mul]; ring
  have hdetm : Matrix.det (h : Matrix (Fin 2) (Fin 2) K₀) = Matrix.det (m : Matrix (Fin 2) (Fin 2) K₀) * c ^ 2 := by
    rw [Matrix.det_fin_two, Matrix.det_fin_two, e, e, e, e]; ring

  have hint' : ∀ i j, IsLocalization.IsInteger R ((m : Matrix (Fin 2) (Fin 2) K₀) i j) := fun i j => hv _ (hle i j)
  choose f hf using hint'
  have hint2 : ∀ i j, IsLocalization.IsInteger R ((m : Matrix (Fin 2) (Fin 2) K₀) i j) := fun i j => ⟨f i j, hf i j⟩
  set d : R := f 0 0 * f 1 1 - f 0 1 * f 1 0 with hd_def
  have hd : algebraMap R K₀ d = Matrix.det (m : Matrix (Fin 2) (Fin 2) K₀) := by
    rw [Matrix.det_fin_two, hd_def, map_sub, map_mul, map_mul, hf, hf, hf, hf]
  have hd0 : d ≠ 0 := by
    intro h0; apply m.det_ne_zero; rw [← hd, h0, map_zero]
  obtain ⟨k, x, hdx⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd0 hϖ
  have hdet : Matrix.det (m : Matrix (Fin 2) (Fin 2) K₀) = algebraMap R K₀ x * algebraMap R K₀ ϖ ^ k := by
    rw [← hd, hdx, map_mul, map_pow]
  have hvdet : Valued.v (algebraMap K₀ K (Matrix.det (m : Matrix (Fin 2) (Fin 2) K₀))) = q ^ k := by
    rw [hdet, map_mul, map_pow, Valuation.map_mul, Valuation.map_pow, hunit x, one_mul]

  have hcart := CerednikDrinfeld.BruhatTits.dist_stdVertex_smul_stdVertex_eq_of_isInteger_of_det_eq_of_isUnit
    R K₀ ϖ hϖ m hint2 k x hdet ⟨i₀, j₀, 1, by rw [Units.val_one, map_one]; exact hone⟩
  rw [hmv] at hcart

  have hk : k ≠ 0 := by
    intro hk0
    apply hne
    have hconn := (CerednikDrinfeld.BruhatTits.tree_isTree R K₀).isConnected
    exact ((hconn.dist_eq_zero_iff).1 (hcart.trans hk0)).symm

  have hone' : ∃ i j : Fin 2, Valued.v (algebraMap K₀ K ((m : Matrix (Fin 2) (Fin 2) K₀) i j)) = 1 :=
    ⟨i₀, j₀, by rw [show (m : Matrix (Fin 2) (Fin 2) K₀) i₀ j₀ = 1 from hone, map_one, Valuation.map_one]⟩
  have hlt : Valued.v (algebraMap K₀ K (Matrix.det (m : Matrix (Fin 2) (Fin 2) K₀))) < 1 := by
    rw [hvdet]; exact pow_lt_one₀ zero_le' hq1 hk
  have hSm : Valued.v (S w u (m : Matrix (Fin 2) (Fin 2) K₀)) = 1 :=
    v_phi_eq_one_of_mem_affinoid_zero_of_v_det_lt_one ϖ₁ hw hu (m : Matrix (Fin 2) (Fin 2) K₀) hle hone' hlt
  have hvc : Valued.v (algebraMap K₀ K c) ≠ 0 := by
    rw [ne_eq, Valuation.zero_iff, map_eq_zero_iff _ hinjK]; exact hc
  refine ⟨?_, ?_⟩
  · rw [hS]
    have hSm0 : Valued.v (S w u (m : Matrix (Fin 2) (Fin 2) K₀)) ≠ 0 := by rw [hSm]; exact one_ne_zero
    exact mul_ne_zero ((Valuation.ne_zero_iff Valued.v).1 hvc) ((Valuation.ne_zero_iff Valued.v).1 hSm0)
  · rw [hS, Valuation.map_mul, hSm, mul_one, hcart, hdetm, map_mul, map_pow, Valuation.map_mul, Valuation.map_pow,
      hvdet, mul_comm]

end Law3CRV

theorem solution
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ)
    (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (ϖ₁ : PseudoUniformizer K₀ K) [DecidableEq (LT.LatticeTree.Vertex R K₀)]
    (g₁ g₂ g₃ g₄ : GL (Fin 2) K₀) {w₁ w₂ w₃ w₄ : K}
    (hw₁ : w₁ ∈ affinoid ϖ₁ 0) (hw₂ : w₂ ∈ affinoid ϖ₁ 0) (hw₃ : w₃ ∈ affinoid ϖ₁ 0) (hw₄ : w₄ ∈ affinoid ϖ₁ 0)
    (h13 : g₁ • LT.LatticeTree.stdVertex R K₀ ≠ g₃ • LT.LatticeTree.stdVertex R K₀)
    (h14 : g₁ • LT.LatticeTree.stdVertex R K₀ ≠ g₄ • LT.LatticeTree.stdVertex R K₀)
    (h23 : g₂ • LT.LatticeTree.stdVertex R K₀ ≠ g₃ • LT.LatticeTree.stdVertex R K₀)
    (h24 : g₂ • LT.LatticeTree.stdVertex R K₀ ≠ g₄ • LT.LatticeTree.stdVertex R K₀)
    (P : (CerednikDrinfeld.BruhatTits.tree R K₀).Path (g₁ • LT.LatticeTree.stdVertex R K₀) (g₂ • LT.LatticeTree.stdVertex R K₀))
    (Q : (CerednikDrinfeld.BruhatTits.tree R K₀).Path (g₃ • LT.LatticeTree.stdVertex R K₀) (g₄ • LT.LatticeTree.stdVertex R K₀)) :
    Valued.v (crossRatio (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g₁) w₁) (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g₂) w₂)
        (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g₃) w₃) (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g₄) w₄)) =
      Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^
        (CerednikDrinfeld.Mumford.walkOverlap
          (P : (CerednikDrinfeld.BruhatTits.tree R K₀).Walk (g₁ • LT.LatticeTree.stdVertex R K₀) (g₂ • LT.LatticeTree.stdVertex R K₀))
          (Q : (CerednikDrinfeld.BruhatTits.tree R K₀).Walk (g₃ • LT.LatticeTree.stdVertex R K₀) (g₄ • LT.LatticeTree.stdVertex R K₀))) := by
  classical
  have hinjK : Function.Injective (algebraMap K₀ K) := (algebraMap K₀ K).injective
  have hinjR : Function.Injective (algebraMap R K₀) := IsFractionRing.injective R K₀
  set q : Γ₀ := Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) with hq_def
  have hq0 : q ≠ 0 := by
    rw [hq_def, ne_eq, Valuation.zero_iff, map_eq_zero_iff _ hinjK, map_eq_zero_iff _ hinjR]
    exact hϖ.ne_zero

  have hΩ₁ := affinoid_subset_upperHalfPlane ϖ₁ 0 hw₁
  have hΩ₂ := affinoid_subset_upperHalfPlane ϖ₁ 0 hw₂
  have hΩ₃ := affinoid_subset_upperHalfPlane ϖ₁ 0 hw₃
  have hΩ₄ := affinoid_subset_upperHalfPlane ϖ₁ 0 hw₄

  have rel : ∀ (gi h : GL (Fin 2) K₀) (wi wj : K),
      (algebraMap K₀ K (gi 0 0) * wi + algebraMap K₀ K (gi 0 1)) *
          (algebraMap K₀ K ((gi * h) 1 0) * wj + algebraMap K₀ K ((gi * h) 1 1)) -
        (algebraMap K₀ K (gi 1 0) * wi + algebraMap K₀ K (gi 1 1)) *
          (algebraMap K₀ K ((gi * h) 0 0) * wj + algebraMap K₀ K ((gi * h) 0 1)) =
      algebraMap K₀ K (Matrix.det (gi : Matrix (Fin 2) (Fin 2) K₀)) *
        Law3CRV.S wi wj (h : Matrix (Fin 2) (Fin 2) K₀) := by
    intro gi h wi wj
    have e : ∀ k l : Fin 2, (gi * h) k l = gi k 0 * h 0 l + gi k 1 * h 1 l := by
      intro k l
      show ((gi : Matrix (Fin 2) (Fin 2) K₀) * (h : Matrix (Fin 2) (Fin 2) K₀)) k l = _
      rw [Matrix.mul_apply, Fin.sum_univ_two]
    simp only [e, Law3CRV.S, Matrix.det_fin_two, map_add, map_mul, map_sub]
    ring

  set h₁₃ : GL (Fin 2) K₀ := g₁⁻¹ * g₃
  set h₂₄ : GL (Fin 2) K₀ := g₂⁻¹ * g₄
  set h₁₄ : GL (Fin 2) K₀ := g₁⁻¹ * g₄
  set h₂₃ : GL (Fin 2) K₀ := g₂⁻¹ * g₃
  have e₁₃ : g₁ * h₁₃ = g₃ := mul_inv_cancel_left g₁ g₃
  have e₂₄ : g₂ * h₂₄ = g₄ := mul_inv_cancel_left g₂ g₄
  have e₁₄ : g₁ * h₁₄ = g₄ := mul_inv_cancel_left g₁ g₄
  have e₂₃ : g₂ * h₂₃ = g₃ := mul_inv_cancel_left g₂ g₃

  have mv : ∀ (gi gj h : GL (Fin 2) K₀), gi * h = gj → gi • (LT.LatticeTree.stdVertex R K₀) ≠ gj • (LT.LatticeTree.stdVertex R K₀) → h • (LT.LatticeTree.stdVertex R K₀) ≠ (LT.LatticeTree.stdVertex R K₀) := by
    intro gi gj h hh hij hfix
    apply hij
    rw [← hh, mul_smul, hfix]
  obtain ⟨n₁₃, k₁₃⟩ := Law3CRV.key R K₀ ϖ hϖ K hint hv ϖ₁ hw₁ hw₃ h₁₃ (mv g₁ g₃ h₁₃ e₁₃ h13)
  obtain ⟨n₂₄, k₂₄⟩ := Law3CRV.key R K₀ ϖ hϖ K hint hv ϖ₁ hw₂ hw₄ h₂₄ (mv g₂ g₄ h₂₄ e₂₄ h24)
  obtain ⟨n₁₄, k₁₄⟩ := Law3CRV.key R K₀ ϖ hϖ K hint hv ϖ₁ hw₁ hw₄ h₁₄ (mv g₁ g₄ h₁₄ e₁₄ h14)
  obtain ⟨n₂₃, k₂₃⟩ := Law3CRV.key R K₀ ϖ hϖ K hint hv ϖ₁ hw₂ hw₃ h₂₃ (mv g₂ g₃ h₂₃ e₂₃ h23)

  have di : ∀ (gi gj h : GL (Fin 2) K₀), gi * h = gj →
      (CerednikDrinfeld.BruhatTits.tree R K₀).dist (LT.LatticeTree.stdVertex R K₀) (h • (LT.LatticeTree.stdVertex R K₀)) = (CerednikDrinfeld.BruhatTits.tree R K₀).dist (gi • (LT.LatticeTree.stdVertex R K₀)) (gj • (LT.LatticeTree.stdVertex R K₀)) := by
    intro gi gj h hh
    rw [← CerednikDrinfeld.Mumford.GraphAction.dist_smul_smul (CerednikDrinfeld.BruhatTits.tree R K₀) gi (LT.LatticeTree.stdVertex R K₀) (h • (LT.LatticeTree.stdVertex R K₀)), ← mul_smul, hh]
  rw [di g₁ g₃ h₁₃ e₁₃] at k₁₃
  rw [di g₂ g₄ h₂₄ e₂₄] at k₂₄
  rw [di g₁ g₄ h₁₄ e₁₄] at k₁₄
  rw [di g₂ g₃ h₂₃ e₂₃] at k₂₃

  have hdd : Matrix.det (h₁₃ : Matrix (Fin 2) (Fin 2) K₀) * Matrix.det (h₂₄ : Matrix (Fin 2) (Fin 2) K₀) =
      Matrix.det (h₁₄ : Matrix (Fin 2) (Fin 2) K₀) * Matrix.det (h₂₃ : Matrix (Fin 2) (Fin 2) K₀) := by
    simp only [h₁₃, h₂₄, h₁₄, h₂₃, Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul]
    ring
  have hH : Valued.v (algebraMap K₀ K (Matrix.det (h₁₃ : Matrix (Fin 2) (Fin 2) K₀))) *
      Valued.v (algebraMap K₀ K (Matrix.det (h₂₄ : Matrix (Fin 2) (Fin 2) K₀))) =
      Valued.v (algebraMap K₀ K (Matrix.det (h₁₄ : Matrix (Fin 2) (Fin 2) K₀))) *
      Valued.v (algebraMap K₀ K (Matrix.det (h₂₃ : Matrix (Fin 2) (Fin 2) K₀))) := by
    rw [← Valuation.map_mul, ← map_mul, hdd, map_mul, Valuation.map_mul]

  have hcr := crossRatio_pmoebius_eq_div_symp g₁ g₂ g₃ g₄ hΩ₁ hΩ₂ hΩ₃ hΩ₄
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hcr
  have r₁₃ := rel g₁ h₁₃ w₁ w₃
  have r₂₄ := rel g₂ h₂₄ w₂ w₄
  have r₁₄ := rel g₁ h₁₄ w₁ w₄
  have r₂₃ := rel g₂ h₂₃ w₂ w₃
  rw [e₁₃] at r₁₃; rw [e₂₄] at r₂₄; rw [e₁₄] at r₁₄; rw [e₂₃] at r₂₃
  rw [r₁₃, r₂₄, r₁₄, r₂₃] at hcr
  have hd₁ : algebraMap K₀ K (Matrix.det (g₁ : Matrix (Fin 2) (Fin 2) K₀)) ≠ 0 :=
    (map_ne_zero_iff _ hinjK).2 g₁.det_ne_zero
  have hd₂ : algebraMap K₀ K (Matrix.det (g₂ : Matrix (Fin 2) (Fin 2) K₀)) ≠ 0 :=
    (map_ne_zero_iff _ hinjK).2 g₂.det_ne_zero

  set S₁₃ := Law3CRV.S w₁ w₃ (h₁₃ : Matrix (Fin 2) (Fin 2) K₀)
  set S₂₄ := Law3CRV.S w₂ w₄ (h₂₄ : Matrix (Fin 2) (Fin 2) K₀)
  set S₁₄ := Law3CRV.S w₁ w₄ (h₁₄ : Matrix (Fin 2) (Fin 2) K₀)
  set S₂₃ := Law3CRV.S w₂ w₃ (h₂₃ : Matrix (Fin 2) (Fin 2) K₀)
  set δ₁ := algebraMap K₀ K (Matrix.det (g₁ : Matrix (Fin 2) (Fin 2) K₀))
  set δ₂ := algebraMap K₀ K (Matrix.det (g₂ : Matrix (Fin 2) (Fin 2) K₀))
  have hcr' : crossRatio (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g₁) w₁) (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g₂) w₂)
      (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g₃) w₃) (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g₄) w₄) =
      (S₁₃ * S₂₄) / (S₁₄ * S₂₃) := by
    rw [hcr, show δ₁ * S₁₃ * (δ₂ * S₂₄) = δ₁ * δ₂ * (S₁₃ * S₂₄) by ring,
      show δ₁ * S₁₄ * (δ₂ * S₂₃) = δ₁ * δ₂ * (S₁₄ * S₂₃) by ring, mul_div_mul_left _ _ (mul_ne_zero hd₁ hd₂)]
  rw [hcr', map_div₀, Valuation.map_mul, Valuation.map_mul]

  set X₁₃ := Valued.v S₁₃
  set X₂₄ := Valued.v S₂₄
  set X₁₄ := Valued.v S₁₄
  set X₂₃ := Valued.v S₂₃
  have X0 : X₁₄ * X₂₃ ≠ 0 :=
    mul_ne_zero ((Valuation.ne_zero_iff Valued.v).2 n₁₄) ((Valuation.ne_zero_iff Valued.v).2 n₂₃)

  have h4 := CerednikDrinfeld.Mumford.dist_add_dist_sub_dist_sub_dist_eq_two_mul_walkOverlap (CerednikDrinfeld.BruhatTits.tree R K₀)
    (CerednikDrinfeld.BruhatTits.tree_isTree R K₀) (P : (CerednikDrinfeld.BruhatTits.tree R K₀).Walk (g₁ • (LT.LatticeTree.stdVertex R K₀)) (g₂ • (LT.LatticeTree.stdVertex R K₀))) (Q : (CerednikDrinfeld.BruhatTits.tree R K₀).Walk (g₃ • (LT.LatticeTree.stdVertex R K₀)) (g₄ • (LT.LatticeTree.stdVertex R K₀)))

  set ov := CerednikDrinfeld.Mumford.walkOverlap (P : (CerednikDrinfeld.BruhatTits.tree R K₀).Walk (g₁ • (LT.LatticeTree.stdVertex R K₀)) (g₂ • (LT.LatticeTree.stdVertex R K₀))) (Q : (CerednikDrinfeld.BruhatTits.tree R K₀).Walk (g₃ • (LT.LatticeTree.stdVertex R K₀)) (g₄ • (LT.LatticeTree.stdVertex R K₀)))
  set d₁₃ := (CerednikDrinfeld.BruhatTits.tree R K₀).dist (g₁ • (LT.LatticeTree.stdVertex R K₀)) (g₃ • (LT.LatticeTree.stdVertex R K₀))
  set d₂₄ := (CerednikDrinfeld.BruhatTits.tree R K₀).dist (g₂ • (LT.LatticeTree.stdVertex R K₀)) (g₄ • (LT.LatticeTree.stdVertex R K₀))
  set d₁₄ := (CerednikDrinfeld.BruhatTits.tree R K₀).dist (g₁ • (LT.LatticeTree.stdVertex R K₀)) (g₄ • (LT.LatticeTree.stdVertex R K₀))
  set d₂₃ := (CerednikDrinfeld.BruhatTits.tree R K₀).dist (g₂ • (LT.LatticeTree.stdVertex R K₀)) (g₃ • (LT.LatticeTree.stdVertex R K₀))

  have hsq : (X₁₃ * X₂₄ / (X₁₄ * X₂₃)) ^ 2 = (q ^ ov) ^ 2 := by
    have hR : (q ^ ov) ^ 2 = q ^ (d₁₄ + d₂₃) / q ^ (d₁₃ + d₂₄) := by
      have hexp : ov * (2 : ℕ) = ((d₁₄ + d₂₃ : ℕ) : ℤ) - ((d₁₃ + d₂₄ : ℕ) : ℤ) := by
        push_cast; linarith [h4]
      conv_lhs => rw [← zpow_natCast (q ^ ov) 2, ← zpow_mul, hexp]
      rw [zpow_sub₀ hq0, zpow_natCast, zpow_natCast]
    rw [hR, div_pow, mul_pow, mul_pow,
      div_eq_div_iff (pow_ne_zero 2 X0 |>.symm.symm |> fun h => by rw [← mul_pow]; exact pow_ne_zero 2 X0)
        (pow_ne_zero _ hq0)]
    rw [pow_add, pow_add]
    calc X₁₃ ^ 2 * X₂₄ ^ 2 * (q ^ d₁₃ * q ^ d₂₄)
        = (X₁₃ ^ 2 * q ^ d₁₃) * (X₂₄ ^ 2 * q ^ d₂₄) := by ac_rfl
      _ = _ := by rw [k₁₃, k₂₄]
      _ = _ := hH
      _ = (X₁₄ ^ 2 * q ^ d₁₄) * (X₂₃ ^ 2 * q ^ d₂₃) := by rw [k₁₄, k₂₃]
      _ = q ^ d₁₄ * q ^ d₂₃ * (X₁₄ ^ 2 * X₂₃ ^ 2) := by ac_rfl
  exact (sq_eq_sq₀ zero_le' zero_le').1 hsq

end S_CerednikDrinfeld_Omega_v_crossRatio_pmoebius_eq_zpow_walkOverlap
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_v_crossRatio_pmoebius_eq_zpow_walkOverlap (solution)
