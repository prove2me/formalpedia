-- Prove2me | solution 1 for CerednikDrinfeld.Omega.eq_one_of_pmoebius_eq_of_mem_affinoid_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/92e8e98a-6ad3-5f5a-a269-2845343afe91

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Theorems.Thm_CerednikDrinfeld_Omega_smul_stdVertex_eq_of_mem_affinoid_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_eq_one_of_pmoebius_eq_of_mem_affinoid_zero
p2m_attr_erase "simp" "LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq LocalGL2.swapUnit_val"

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega CerednikDrinfeld.Mumford MulAction

theorem solution
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ)
    (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (ϖ₁ : PseudoUniformizer K₀ K)
    {G : Type} [Group G] [MulAction G (LT.LatticeTree.Vertex R K₀)]
    [CerednikDrinfeld.Mumford.GraphAction G (CerednikDrinfeld.BruhatTits.tree R K₀)]
    (ρ : G →* PGL(2, K₀)) (hρ : CerednikDrinfeld.Mumford.ActsThrough (LT.LatticeTree.Vertex R K₀) ρ)
    (hS : CerednikDrinfeld.Mumford.IsSchottky G (CerednikDrinfeld.BruhatTits.tree R K₀))
    (g : GL (Fin 2) K₀) {w w' : K} (hw : w ∈ affinoid ϖ₁ 0) (hw' : w' ∈ affinoid ϖ₁ 0) (γ : G)
    (h : pmoebius K₀ (ρ γ) (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g) w) =
           pmoebius K₀ (Matrix.ProjGenLinGroup.mk g) w') :
    γ = 1 ∧ w = w' := by
  classical
  have hwΩ : w ∈ upperHalfPlane K₀ K := affinoid_subset_upperHalfPlane ϖ₁ 0 hw
  have hw'Ω : w' ∈ upperHalfPlane K₀ K := affinoid_subset_upperHalfPlane ϖ₁ 0 hw'

  have hinv : ∀ (p : PGL(2, K₀)) {y : K}, y ∈ upperHalfPlane K₀ K → pmoebius K₀ p⁻¹ (pmoebius K₀ p y) = y := by
    intro p y hy
    rw [← pmoebius_mul K₀ hy, inv_mul_cancel]
    have h11 := pmoebius_mul K₀ hy (1 : PGL(2, K₀)) 1
    rw [one_mul] at h11
    simp [pmoebius]

  obtain ⟨c, hc⟩ := Matrix.ProjGenLinGroup.mk_surjective (ρ γ)
  set x : K := pmoebius K₀ (Matrix.ProjGenLinGroup.mk g) w' with hx_def
  have hL : pmoebius K₀ (Matrix.ProjGenLinGroup.mk (c * g)) w = x := by
    rw [map_mul, hc, pmoebius_mul K₀ hwΩ]; exact h
  have hx1 : pmoebius K₀ (Matrix.ProjGenLinGroup.mk (c * g))⁻¹ x ∈ affinoid ϖ₁ 0 := by
    rw [← hL, hinv _ hwΩ]; exact hw
  have hx2 : pmoebius K₀ (Matrix.ProjGenLinGroup.mk g)⁻¹ x ∈ affinoid ϖ₁ 0 := by
    rw [hx_def, hinv _ hw'Ω]; exact hw'
  have hvert := smul_stdVertex_eq_of_mem_affinoid_zero R K₀ ϖ hϖ K hint hv ϖ₁ (c * g) g hx1 hx2

  have hγ : γ = 1 := by
    have hfix : γ • (g • LT.LatticeTree.stdVertex R K₀) = g • LT.LatticeTree.stdVertex R K₀ := by
      rw [hρ γ, ← hc, CerednikDrinfeld.BruhatTits.pgl_mk_smul, ← mul_smul]; exact hvert
    have hmem : γ ∈ stabilizer G (g • LT.LatticeTree.stdVertex R K₀) := hfix
    rw [hS.stabilizer_eq_bot] at hmem
    exact hmem
  refine ⟨hγ, ?_⟩
  subst hγ
  rw [map_one] at h
  have h1y : ∀ (y : K), pmoebius K₀ (1 : PGL(2, K₀)) y = y := by
    intro y; simp [pmoebius]
  rw [h1y, hx_def] at h
  have := congrArg (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g)⁻¹) h
  rwa [hinv _ hwΩ, hinv _ hw'Ω] at this

end S_CerednikDrinfeld_Omega_eq_one_of_pmoebius_eq_of_mem_affinoid_zero
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_eq_one_of_pmoebius_eq_of_mem_affinoid_zero (solution)
