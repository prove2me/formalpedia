-- Prove2me | solution 1 for CerednikDrinfeld.Omega.isDiscrete_of_finite_stabilizer_stdVertex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/69cd1c46-7c14-5331-9c67-7e7d5128093b

import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Theorems.Thm_LT_LatticeTree_finite_setOf_isWithin_and_card_eq
import Theorems.Thm_LT_LatticeTree_Vertex_isWithin_stdVertex_act_of_isInteger_of_det_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_isDiscrete_of_finite_stabilizer_stdVertex

set_option autoImplicit false

open scoped MatrixGroups

theorem solution
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (K : Type) [Field K] [Algebra K₀ K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (hq : ∀ ε : Γ₀, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ N ≤ ε)
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀))
    (hst : {γ : G | ρ γ • LT.LatticeTree.stdVertex R K₀ = LT.LatticeTree.stdVertex R K₀}.Finite) :
    CerednikDrinfeld.Omega.IsDiscrete K ρ := by
  classical
  intro ε hε
  obtain ⟨N, hN⟩ := hq ε hε
  let v₀ : LT.LatticeTree.Vertex R K₀ := LT.LatticeTree.stdVertex R K₀
  let B : ℕ → Set (LT.LatticeTree.Vertex R K₀) := fun d =>
    {w | LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K₀) hϖ.ne_zero) d v₀ w}
  have hB : ∀ d, (B d).Finite := fun d =>
    (LT.LatticeTree.finite_setOf_isWithin_and_card_eq R K₀ ϖ hϖ v₀ d).1
  let S : Set (LT.LatticeTree.Vertex R K₀) := ⋃ d ∈ Finset.range (N + 1), B d
  have hS : S.Finite := Set.Finite.biUnion (Finset.finite_toSet _) (fun d _ => hB d)

  have hfib : ∀ w : LT.LatticeTree.Vertex R K₀, {γ : G | ρ γ • v₀ = w}.Finite := by
    intro w
    by_cases hw : ∃ γ₁ : G, ρ γ₁ • v₀ = w
    · obtain ⟨γ₁, hγ₁⟩ := hw
      refine (hst.image (fun σ => γ₁ * σ)).subset ?_
      intro γ hγ
      refine ⟨γ₁⁻¹ * γ, ?_, by group⟩
      show ρ (γ₁⁻¹ * γ) • v₀ = v₀
      rw [map_mul, mul_smul, map_inv, inv_smul_eq_iff]
      exact (hγ.trans hγ₁.symm)
    · push_neg at hw
      convert Set.finite_empty
      ext γ; simpa using hw γ
  have hT : {γ : G | ρ γ • v₀ ∈ S}.Finite := by
    have h1 : {γ : G | ρ γ • v₀ ∈ S} = ⋃ w ∈ S, {γ : G | ρ γ • v₀ = w} := by
      ext γ; simp
    rw [h1]; exact hS.biUnion (fun w _ => hfib w)
  refine hT.subset ?_
  rintro γ ⟨g, hg, hle, hεle⟩
  have hint' : ∀ i j, IsLocalization.IsInteger R ((g : Matrix (Fin 2) (Fin 2) K₀) i j) :=
    fun i j => hv _ (hle i j)

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

  have hunit : ∀ w : Rˣ, Valued.v (algebraMap K₀ K (algebraMap R K₀ (w : R))) = 1 := by
    intro w
    apply le_antisymm (hint w)
    have h := hint (w⁻¹ : Rˣ)
    have hprod : Valued.v (algebraMap K₀ K (algebraMap R K₀ (w : R))) *
        Valued.v (algebraMap K₀ K (algebraMap R K₀ ((w⁻¹ : Rˣ) : R))) = 1 := by
      rw [← Valuation.map_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, Valuation.map_one]
    calc (1 : Γ₀) = _ := hprod.symm
      _ ≤ Valued.v (algebraMap K₀ K (algebraMap R K₀ (w : R))) * 1 := mul_le_mul_right h _
      _ = _ := mul_one _

  choose f hf using hint'
  have hint2 : ∀ i j, IsLocalization.IsInteger R ((g : Matrix (Fin 2) (Fin 2) K₀) i j) := fun i j => ⟨f i j, hf i j⟩
  set d : R := f 0 0 * f 1 1 - f 0 1 * f 1 0 with hd_def
  have hd : algebraMap R K₀ d = Matrix.det (g : Matrix (Fin 2) (Fin 2) K₀) := by
    rw [Matrix.det_fin_two, hd_def, map_sub, map_mul, map_mul, hf, hf, hf, hf]
  have hd0 : d ≠ 0 := by
    intro h0
    apply (g : GL (Fin 2) K₀).det_ne_zero
    rw [← hd, h0, map_zero]
  obtain ⟨k, u, hdu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd0 hϖ
  have hdet : Matrix.det (g : Matrix (Fin 2) (Fin 2) K₀) = algebraMap R K₀ u * algebraMap R K₀ ϖ ^ k := by
    rw [← hd, hdu, map_mul, map_pow]
  have hvdet : Valued.v (algebraMap K₀ K (Matrix.det (g : Matrix (Fin 2) (Fin 2) K₀))) = q ^ k := by
    rw [hdet, map_mul, map_pow, Valuation.map_mul, Valuation.map_pow, hunit u, one_mul]
  have hkN : k ≤ N := by
    by_contra hlt
    push_neg at hlt
    have h1 : q ^ k < q ^ N := pow_lt_pow_right_of_lt_one₀ (zero_lt_iff.2 hq0) hq1 hlt
    exact absurd (hN.trans (hvdet ▸ hεle)) (not_le.2 h1)
  have hw := LT.LatticeTree.Vertex.isWithin_stdVertex_act_of_isInteger_of_det_eq R K₀ ϖ hϖ g hint2 k u hdet
  have hγ : ρ γ • v₀ = LT.LatticeTree.Vertex.act g v₀ := by
    rw [← hg]; rfl
  show ρ γ • v₀ ∈ S
  simp only [S, Set.mem_iUnion, B, Set.mem_setOf_eq]
  exact ⟨k, Finset.mem_range.2 (Nat.lt_succ_of_le hkN), hγ ▸ hw⟩

end S_CerednikDrinfeld_Omega_isDiscrete_of_finite_stabilizer_stdVertex
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_isDiscrete_of_finite_stabilizer_stdVertex (solution)
