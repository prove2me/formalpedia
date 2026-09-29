-- Prove2me | solution 1 for CerednikDrinfeld.Omega.v_theta_pmoebius_eq_zpow_neg_sum_stabWidth_mul_pathCycle_mul_walkCycle
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/173da3bc-d2de-5343-a021-7c6bec06b608

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_WalkOverlap
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import Theorems.Thm_CerednikDrinfeld_Omega_v_crossRatio_pmoebius_eq_zpow_walkOverlap
import Theorems.Thm_CerednikDrinfeld_Mumford_finsum_walkOverlap_map_smulHom_eq_sum_stabWidth_mul_walkCycle_mul_walkCycle
import Theorems.Thm_CerednikDrinfeld_Mumford_finite_setOf_exists_mem_darts_smul_mem_darts
import Theorems.Thm_Valued_v_tprod_eq_finsetProd_of_forall_not_mem_v_eq_one
import Theorems.Thm_CerednikDrinfeld_Omega_thetaMultipliable_of_isDiscrete_of_mem_affinoid
import Theorems.Thm_CerednikDrinfeld_Omega_isDiscrete_of_finite_stabilizer_stdVertex
import Theorems.Thm_CerednikDrinfeld_BruhatTits_tree_isTree
import Theorems.Thm_CerednikDrinfeld_Mumford_pathCycle_eq_pathCycle_of_isTree
import Theorems.Thm_CerednikDrinfeld_Mumford_dist_add_dist_sub_dist_sub_dist_eq_two_mul_walkOverlap
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_eq_zpow_neg_sum_stabWidth_mul_pathCycle_mul_walkCycle
p2m_attr_erase "simp" "LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq LocalGL2.swapUnit_val"

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega CerednikDrinfeld.Mumford MulAction

namespace Law3T5P

theorem prod_zpow_eq_zpow_sum {Γ₀ : Type} [CommGroupWithZero Γ₀] (q : Γ₀) (hq : q ≠ 0)
    {ι : Type} (s : Finset ι) (f : ι → ℤ) : ∏ i ∈ s, q ^ f i = q ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hq]

theorem walkOverlap_map_smulHom_eq_zero
    {G : Type} [Group G] {W : Type} [DecidableEq W] [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
    {u v u' v' : W} (P : 𝒯.Walk u v) (Q : 𝒯.Walk u' v') (γ : G)
    (h : ¬ ∃ d ∈ Q.darts, γ • d ∈ P.darts ∨ (γ • d).symm ∈ P.darts) :
    walkOverlap P (Q.map (smulHom γ)) = 0 := by
  classical
  push_neg at h
  unfold walkOverlap
  apply List.sum_eq_zero
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨d, hd, rfl⟩ := hx
  have hdarts : (Q.map (smulHom (𝒯 := 𝒯) γ)).darts = Q.darts.map (fun d' => γ • d') := by
    rw [SimpleGraph.Walk.darts_map]; rfl
  rw [hdarts]
  have h1 : (Q.darts.map (fun d' => γ • d')).count d = 0 := by
    rw [List.count_eq_zero, List.mem_map]
    rintro ⟨d', hd', rfl⟩
    exact (h d' hd').1 hd
  have h2 : (Q.darts.map (fun d' => γ • d')).count d.symm = 0 := by
    rw [List.count_eq_zero, List.mem_map]
    rintro ⟨d', hd', hd's⟩
    apply (h d' hd').2
    rw [hd's, SimpleGraph.Dart.symm_symm]; exact hd
  rw [h1, h2]; simp

end Law3T5P

theorem solution
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (hq : ∀ ε : Γ₀, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ N ≤ ε)
    (ϖ₁ : PseudoUniformizer K₀ K)
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀))
    [MulAction G (LT.LatticeTree.Vertex R K₀)]
    [CerednikDrinfeld.Mumford.GraphAction G (CerednikDrinfeld.BruhatTits.tree R K₀)]
    (hρ : CerednikDrinfeld.Mumford.ActsThrough (LT.LatticeTree.Vertex R K₀) ρ)
    (hfin : ∀ w : LT.LatticeTree.Vertex R K₀, Finite (MulAction.stabilizer G w))
    (τ : LT.LatticeTree.Vertex R K₀ → ZMod 2) (hτ : ∀ (g : G) (w : LT.LatticeTree.Vertex R K₀), τ (g • w) = τ w)
    (hadj : ∀ u w : LT.LatticeTree.Vertex R K₀, (CerednikDrinfeld.BruhatTits.tree R K₀).Adj u w → τ u ≠ τ w)
    [DecidableEq (CerednikDrinfeld.Mumford.QuotEdge G (CerednikDrinfeld.BruhatTits.tree R K₀))]
    {E : Type} [Fintype E]
    (eE : E ≃ {e : CerednikDrinfeld.Mumford.QuotEdge G (CerednikDrinfeld.BruhatTits.tree R K₀) // τ e.out.fst = 0})
    (gₐ g g' : GL (Fin 2) K₀) {wₐ w w' : K}
    (hwₐ : wₐ ∈ affinoid ϖ₁ 0) (hw : w ∈ affinoid ϖ₁ 0) (hw' : w' ∈ affinoid ϖ₁ 0)
    (hsep  : τ (g • LT.LatticeTree.stdVertex R K₀)  ≠ τ (gₐ • LT.LatticeTree.stdVertex R K₀))
    (hsep' : τ (g' • LT.LatticeTree.stdVertex R K₀) ≠ τ (gₐ • LT.LatticeTree.stdVertex R K₀))
    [DecidableEq (LT.LatticeTree.Vertex R K₀)]
    (P : (CerednikDrinfeld.BruhatTits.tree R K₀).Walk (g • LT.LatticeTree.stdVertex R K₀) (g' • LT.LatticeTree.stdVertex R K₀))
    (α : G) :
    Valued.v (theta ρ (pmoebius K₀ (Matrix.ProjGenLinGroup.mk gₐ) wₐ)
                       (pmoebius K₀ (ρ α) (pmoebius K₀ (Matrix.ProjGenLinGroup.mk gₐ) wₐ))
                       (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g) w)
                       (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g') w')) =
      Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^
        (-(∑ e : E, ((CerednikDrinfeld.Mumford.stabWidth G (CerednikDrinfeld.BruhatTits.tree R K₀) (eE e).1 : ℕ) : ℤ) *
            CerednikDrinfeld.Mumford.pathCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e => (eE e).1)
                (LT.LatticeTree.stdVertex R K₀) α e *
            CerednikDrinfeld.Mumford.walkCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e => (eE e).1) P e)) := by

  have hinjK : Function.Injective (algebraMap K₀ K) := (algebraMap K₀ K).injective
  have hinjR : Function.Injective (algebraMap R K₀) := IsFractionRing.injective R K₀
  have hq0 : Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ≠ 0 := by
    rw [ne_eq, Valuation.zero_iff, map_eq_zero_iff _ hinjK, map_eq_zero_iff _ hinjR]; exact hϖ.ne_zero
  have hTree := CerednikDrinfeld.BruhatTits.tree_isTree R K₀
  have hΩₐ : wₐ ∈ upperHalfPlane K₀ K := affinoid_subset_upperHalfPlane ϖ₁ 0 hwₐ
  have hΩw : w ∈ upperHalfPlane K₀ K := affinoid_subset_upperHalfPlane ϖ₁ 0 hw
  have hΩw' : w' ∈ upperHalfPlane K₀ K := affinoid_subset_upperHalfPlane ϖ₁ 0 hw'

  choose c hc using fun γ : G => Matrix.ProjGenLinGroup.mk_surjective (ρ γ)

  have actv : ∀ (γ : G) (gl : GL (Fin 2) K₀),
      γ • (gl • (LT.LatticeTree.stdVertex R K₀)) = (c γ * gl) • (LT.LatticeTree.stdVertex R K₀) := by
    intro γ gl
    rw [hρ γ, ← hc γ, CerednikDrinfeld.BruhatTits.pgl_mk_smul, mul_smul]
  have actp : ∀ (γ : G) (gl : GL (Fin 2) K₀) {x : K}, x ∈ upperHalfPlane K₀ K →
      pmoebius K₀ (ρ γ) (pmoebius K₀ (Matrix.ProjGenLinGroup.mk gl) x) =
        pmoebius K₀ (Matrix.ProjGenLinGroup.mk (c γ * gl)) x := by
    intro γ gl x hx
    rw [← hc γ, ← pmoebius_mul K₀ hx, ← map_mul]
  have τc : ∀ (γ : G) (gl : GL (Fin 2) K₀), τ ((c γ * gl) • (LT.LatticeTree.stdVertex R K₀)) = τ (gl • (LT.LatticeTree.stdVertex R K₀)) := by
    intro γ gl; rw [← actv, hτ]

  set A := gₐ • (LT.LatticeTree.stdVertex R K₀) with hA
  have hconn := hTree.connected
  let P₀ : (CerednikDrinfeld.BruhatTits.tree R K₀).Path (g' • (LT.LatticeTree.stdVertex R K₀)) (g • (LT.LatticeTree.stdVertex R K₀)) := somePath (hconn.preconnected _ _)
  let Q₀ : (CerednikDrinfeld.BruhatTits.tree R K₀).Path A (α • A) := somePath (hconn.preconnected _ _)

  have hfac : ∀ γ : G,
      Valued.v (thetaFactor ρ (pmoebius K₀ (Matrix.ProjGenLinGroup.mk gₐ) wₐ)
          (pmoebius K₀ (ρ α) (pmoebius K₀ (Matrix.ProjGenLinGroup.mk gₐ) wₐ))
          (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g) w)
          (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g') w') γ) =
        Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^
          walkOverlap P.reverse ((Q₀ : (CerednikDrinfeld.BruhatTits.tree R K₀).Walk A (α • A)).map (smulHom γ)) := by
    intro γ
    unfold thetaFactor
    rw [actp α gₐ hΩₐ, actp γ gₐ hΩₐ, actp γ (c α * gₐ) hΩₐ]
    have e₃ : γ • A = (c γ * gₐ) • (LT.LatticeTree.stdVertex R K₀) := by rw [hA, actv]
    have e₄ : γ • (α • A) = (c γ * (c α * gₐ)) • (LT.LatticeTree.stdVertex R K₀) := by rw [hA, actv, actv]
    let Qγ : (CerednikDrinfeld.BruhatTits.tree R K₀).Path (γ • A) (γ • (α • A)) :=
      SimpleGraph.Path.map (smulHom γ) (MulAction.injective γ) Q₀
    let Q₁ : (CerednikDrinfeld.BruhatTits.tree R K₀).Path ((c γ * gₐ) • (LT.LatticeTree.stdVertex R K₀)) ((c γ * (c α * gₐ)) • (LT.LatticeTree.stdVertex R K₀)) :=
      ⟨Qγ.1.copy e₃ e₄, by simpa [SimpleGraph.Walk.isPath_copy] using Qγ.2⟩
    have h13 : g' • (LT.LatticeTree.stdVertex R K₀) ≠ (c γ * gₐ) • (LT.LatticeTree.stdVertex R K₀) := by
      intro h; apply hsep'; rw [h, τc]
    have h14 : g' • (LT.LatticeTree.stdVertex R K₀) ≠ (c γ * (c α * gₐ)) • (LT.LatticeTree.stdVertex R K₀) := by
      intro h; apply hsep'; rw [h, τc, τc]
    have h23 : g • (LT.LatticeTree.stdVertex R K₀) ≠ (c γ * gₐ) • (LT.LatticeTree.stdVertex R K₀) := by
      intro h; apply hsep; rw [h, τc]
    have h24 : g • (LT.LatticeTree.stdVertex R K₀) ≠ (c γ * (c α * gₐ)) • (LT.LatticeTree.stdVertex R K₀) := by
      intro h; apply hsep; rw [h, τc, τc]
    have hcv := v_crossRatio_pmoebius_eq_zpow_walkOverlap R K₀ ϖ hϖ K hint hv ϖ₁
      g' g (c γ * gₐ) (c γ * (c α * gₐ)) hw' hw hwₐ hwₐ h13 h14 h23 h24 P₀ Q₁
    rw [hcv]
    congr 1

    have hcopy : walkOverlap P₀.1 Q₁.1 =
        walkOverlap P₀.1 Qγ.1 := by
      show walkOverlap P₀.1 (Qγ.1.copy e₃ e₄) = _
      simp only [walkOverlap, SimpleGraph.Walk.darts_copy]
    rw [hcopy]
    have f1 := CerednikDrinfeld.Mumford.dist_add_dist_sub_dist_sub_dist_eq_two_mul_walkOverlap (CerednikDrinfeld.BruhatTits.tree R K₀) hTree
      P₀.1 Qγ.1
    have f2 := CerednikDrinfeld.Mumford.dist_add_dist_sub_dist_sub_dist_eq_two_mul_walkOverlap (CerednikDrinfeld.BruhatTits.tree R K₀) hTree
      P.reverse Qγ.1
    have : (2 : ℤ) * walkOverlap P₀.1 Qγ.1 =
        2 * walkOverlap P.reverse Qγ.1 := by rw [← f1, ← f2]
    have := mul_left_cancel₀ (two_ne_zero) this
    exact this

  have hst : {γ : G | ρ γ • (LT.LatticeTree.stdVertex R K₀) = (LT.LatticeTree.stdVertex R K₀)}.Finite := by
    haveI : Finite (stabilizer G (LT.LatticeTree.stdVertex R K₀)) := hfin _
    refine (Set.toFinite ((stabilizer G (LT.LatticeTree.stdVertex R K₀) : Subgroup G) : Set G)).subset ?_
    intro γ hγ
    simp only [Set.mem_setOf_eq] at hγ
    show γ ∈ stabilizer G (LT.LatticeTree.stdVertex R K₀)
    rw [mem_stabilizer_iff, hρ γ]; exact hγ
  have hdisc := isDiscrete_of_finite_stabilizer_stdVertex R K₀ ϖ hϖ K hint hv hq ρ hst
  obtain ⟨m₁, hm₁⟩ := exists_mapsTo_affinoid ϖ₁ (Matrix.ProjGenLinGroup.mk gₐ) 0
  obtain ⟨m₂, hm₂⟩ := exists_mapsTo_affinoid ϖ₁ (ρ α) m₁
  obtain ⟨m₃, hm₃⟩ := exists_mapsTo_affinoid ϖ₁ (Matrix.ProjGenLinGroup.mk g) 0
  obtain ⟨m₄, hm₄⟩ := exists_mapsTo_affinoid ϖ₁ (Matrix.ProjGenLinGroup.mk g') 0
  have ha := hm₁ hwₐ
  have hαa := hm₂ ha
  have hz := hm₃ hw
  have hz' := hm₄ hw'
  have hmono := affinoid_mono ϖ₁
  set N := max (max m₁ m₂) (max m₃ m₄) with hN
  have hmult : ThetaMultipliable ρ (pmoebius K₀ (Matrix.ProjGenLinGroup.mk gₐ) wₐ)
      (pmoebius K₀ (ρ α) (pmoebius K₀ (Matrix.ProjGenLinGroup.mk gₐ) wₐ))
      (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g) w)
      (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g') w') :=
    thetaMultipliable_of_isDiscrete_of_mem_affinoid ϖ₁ ρ hdisc N
      (hmono (le_trans (le_max_left _ _) (le_max_left _ _)) ha)
      (hmono (le_trans (le_max_right _ _) (le_max_left _ _)) hαa)
      (hmono (le_trans (le_max_left _ _) (le_max_right _ _)) hz)
      (hmono (le_trans (le_max_right _ _) (le_max_right _ _)) hz')

  have hSfin := finite_setOf_exists_mem_darts_smul_mem_darts (CerednikDrinfeld.BruhatTits.tree R K₀) hfin
    P.reverse (Q₀ : (CerednikDrinfeld.BruhatTits.tree R K₀).Walk A (α • A))
  set ovf : G → ℤ := fun γ => walkOverlap P.reverse
      ((Q₀ : (CerednikDrinfeld.BruhatTits.tree R K₀).Walk A (α • A)).map (smulHom γ)) with hovf
  have hov0 : ∀ γ : G, γ ∉ hSfin.toFinset → ovf γ = 0 := by
    intro γ hγ
    rw [Set.Finite.mem_toFinset] at hγ
    exact Law3T5P.walkOverlap_map_smulHom_eq_zero (CerednikDrinfeld.BruhatTits.tree R K₀) _ _ γ hγ
  have hsupp : Function.support ovf ⊆ {γ : G | ∃ d ∈ (Q₀ : (CerednikDrinfeld.BruhatTits.tree R K₀).Walk A (α • A)).darts,
      γ • d ∈ P.reverse.darts ∨ (γ • d).symm ∈ P.reverse.darts} := by
    intro γ hγ
    by_contra hnot
    exact hγ (Law3T5P.walkOverlap_map_smulHom_eq_zero (CerednikDrinfeld.BruhatTits.tree R K₀) _ _ γ hnot)
  unfold CerednikDrinfeld.Omega.theta
  rw [Valued.v_tprod_eq_finsetProd_of_forall_not_mem_v_eq_one _ hmult hSfin.toFinset
    (fun γ hγ => by rw [hfac γ, show walkOverlap _ _ = ovf γ from rfl, hov0 γ hγ, zpow_zero])]
  simp_rw [hfac]
  rw [Law3T5P.prod_zpow_eq_zpow_sum _ hq0]
  congr 1

  rw [show (∑ γ ∈ hSfin.toFinset, walkOverlap P.reverse
      ((Q₀ : (CerednikDrinfeld.BruhatTits.tree R K₀).Walk A (α • A)).map (smulHom γ))) = ∑ γ ∈ hSfin.toFinset, ovf γ from rfl,
    ← finsum_eq_sum_of_support_subset_of_finite ovf hsupp hSfin]
  rw [show (∑ᶠ γ, ovf γ) = ∑ᶠ γ : G, walkOverlap P.reverse
      ((Q₀ : (CerednikDrinfeld.BruhatTits.tree R K₀).Walk A (α • A)).map (smulHom γ)) from rfl]
  rw [finsum_walkOverlap_map_smulHom_eq_sum_stabWidth_mul_walkCycle_mul_walkCycle (CerednikDrinfeld.BruhatTits.tree R K₀)
    hfin τ hτ hadj eE]
  have hQc : walkCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e => (eE e).1) (Q₀ : (CerednikDrinfeld.BruhatTits.tree R K₀).Walk A (α • A)) =
      pathCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e => (eE e).1) (LT.LatticeTree.stdVertex R K₀) α := by
    rw [← pathCycle_eq_pathCycle_of_isTree (CerednikDrinfeld.BruhatTits.tree R K₀) hTree (fun e => (eE e).1) (LT.LatticeTree.stdVertex R K₀) A α,
      pathCycle_eq_walkCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e => (eE e).1) hTree.isAcyclic A α Q₀]
  rw [hQc, walkCycle_reverse, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Pi.neg_apply]
  ring

end S_CerednikDrinfeld_Omega_v_theta_pmoebius_eq_zpow_neg_sum_stabWidth_mul_pathCycle_mul_walkCycle
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_eq_zpow_neg_sum_stabWidth_mul_pathCycle_mul_walkCycle (solution)
