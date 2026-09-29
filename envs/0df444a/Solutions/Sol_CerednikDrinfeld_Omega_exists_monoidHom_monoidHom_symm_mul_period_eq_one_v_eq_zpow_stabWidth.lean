-- Prove2me | solution 1 for CerednikDrinfeld.Omega.exists_monoidHom_monoidHom_symm_mul_period_eq_one_v_eq_zpow_stabWidth
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/36a49985-a47a-5040-9374-dcb006fb1738

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import Theorems.Thm_CerednikDrinfeld_Omega_v_period_eq_zpow_neg_sum_stabWidth_mul_pathCycle_mul_pathCycle
import Theorems.Thm_CerednikDrinfeld_Omega_exists_monoidHom_monoidHom_eq_period
import Theorems.Thm_CerednikDrinfeld_Omega_period_symm
import Theorems.Thm_CerednikDrinfeld_Omega_thetaMultipliable_of_isDiscrete_of_isExhausted
import Theorems.Thm_CerednikDrinfeld_Omega_isDiscrete_of_finite_stabilizer_stdVertex
import Theorems.Thm_MonoidHom_exists_subfield_units_coe_eq
import Theorems.Thm_CerednikDrinfeld_Omega_smul_stdVertex_eq_of_mem_affinoid_zero
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_exists_monoidHom_monoidHom_symm_mul_period_eq_one_v_eq_zpow_stabWidth
p2m_attr_erase "simp" "CerednikDrinfeld.Mumford.walkOverlap_nil_right CerednikDrinfeld.Mumford.walkOverlap_nil_left LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq LocalGL2.swapUnit_val"

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega CerednikDrinfeld.Mumford MulAction

theorem solution
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (hq : ∀ ε : Γ₀, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ N ≤ ε)
    (ϖ₁ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ₁)
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
    (g₀ gₐ : GL (Fin 2) K₀) {w₀ wₐ : K} (hw₀ : w₀ ∈ affinoid ϖ₁ 0) (hwₐ : wₐ ∈ affinoid ϖ₁ 0)
    (hsep : τ (g₀ • LT.LatticeTree.stdVertex R K₀) ≠ τ (gₐ • LT.LatticeTree.stdVertex R K₀))
    (Kp : Subfield K)
    (hKp : ∀ α β : G, period ρ (pmoebius K₀ (Matrix.ProjGenLinGroup.mk gₐ) wₐ)
                              (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g₀) w₀) α β ∈ Kp) :
    ∃ Q : G →* G →* (↥Kp)ˣ,
      (∀ α β : G, Q α β = Q β α) ∧
      (∀ α β : G, (((Q α β : (↥Kp)ˣ) : ↥Kp) : K) *
          period ρ (pmoebius K₀ (Matrix.ProjGenLinGroup.mk gₐ) wₐ)
                   (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g₀) w₀) α β = 1) ∧
      (∀ α β : G, Valued.v (((Q α β : (↥Kp)ˣ) : ↥Kp) : K) =
          Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^
            (∑ e : E, ((CerednikDrinfeld.Mumford.stabWidth G (CerednikDrinfeld.BruhatTits.tree R K₀) (eE e).1 : ℕ) : ℤ) *
            CerednikDrinfeld.Mumford.pathCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e => (eE e).1)
                (LT.LatticeTree.stdVertex R K₀) α e *
            CerednikDrinfeld.Mumford.pathCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e => (eE e).1)
                (LT.LatticeTree.stdVertex R K₀) β e)) := by
  classical

  have hinjK : Function.Injective (algebraMap K₀ K) := (algebraMap K₀ K).injective
  have hinjR : Function.Injective (algebraMap R K₀) := IsFractionRing.injective R K₀
  have hq0 : Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ≠ 0 := by
    rw [ne_eq, Valuation.zero_iff, map_eq_zero_iff _ hinjK, map_eq_zero_iff _ hinjR]; exact hϖ.ne_zero
  have hΩₐ : wₐ ∈ upperHalfPlane K₀ K := affinoid_subset_upperHalfPlane ϖ₁ 0 hwₐ
  have hΩ₀ : w₀ ∈ upperHalfPlane K₀ K := affinoid_subset_upperHalfPlane ϖ₁ 0 hw₀

  choose c hc using fun γ : G => Matrix.ProjGenLinGroup.mk_surjective (ρ γ)
  have hinv : ∀ (p : PGL(2, K₀)) {y : K}, y ∈ upperHalfPlane K₀ K → pmoebius K₀ p⁻¹ (pmoebius K₀ p y) = y := by
    intro p y hy
    rw [← pmoebius_mul K₀ hy, inv_mul_cancel]
    simp [pmoebius]

  set sh : ℕ → K := fun n => w₀ + algebraMap K₀ K (ϖ₁.ϖ ^ (n + 1)) with hsh_def
  have hsh_mem : ∀ n, sh n ∈ affinoid ϖ₁ 0 := by
    intro n
    rw [mem_affinoid_iff'] at hw₀ ⊢
    obtain ⟨h0, h1⟩ := hw₀
    simp only [pow_zero] at h0 h1 ⊢
    refine ⟨?_, fun t => ?_⟩
    · refine (Valuation.map_add _ _ _).trans (max_le h0 ?_)
      rw [map_pow, Valuation.map_pow]
      exact pow_le_one₀ zero_le' ϖ₁.lt_one.le
    · have h2 := h1 (t - ϖ₁.ϖ ^ (n + 1))
      rw [RingHom.map_sub] at h2
      have e : sh n - algebraMap K₀ K t = w₀ - (algebraMap K₀ K t - algebraMap K₀ K (ϖ₁.ϖ ^ (n + 1))) := by
        rw [hsh_def]; ring
      rw [e]; exact h2
  have hsh_inj : Function.Injective sh := by
    intro m n h
    have h' : algebraMap K₀ K (ϖ₁.ϖ ^ (m + 1)) = algebraMap K₀ K (ϖ₁.ϖ ^ (n + 1)) := add_left_cancel h
    have h'' := congrArg Valued.v h'
    simp only [map_pow] at h''
    have hinjp : Function.Injective fun k : ℕ => Valued.v (algebraMap K₀ K ϖ₁.ϖ) ^ k :=
      (pow_right_strictAnti₀ ϖ₁.pos ϖ₁.lt_one).injective
    have := hinjp h''
    omega

  have hbad : (Set.range fun γ : ↥(stabilizer G (g₀ • LT.LatticeTree.stdVertex R K₀)) =>
      pmoebius K₀ (Matrix.ProjGenLinGroup.mk g₀)⁻¹
        (pmoebius K₀ (ρ γ) (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g₀) w₀))).Finite := by
    haveI := hfin (g₀ • LT.LatticeTree.stdVertex R K₀)
    exact Set.finite_range _
  obtain ⟨w₁, ⟨n₁, rfl⟩, hw₁bad⟩ := (Set.infinite_range_of_injective hsh_inj).exists_notMem_finite hbad
  have hw₁ : sh n₁ ∈ affinoid ϖ₁ 0 := hsh_mem n₁
  have hΩ₁ : sh n₁ ∈ upperHalfPlane K₀ K := affinoid_subset_upperHalfPlane ϖ₁ 0 hw₁
  have hne01 : w₀ ≠ sh n₁ := by
    intro h
    have : algebraMap K₀ K (ϖ₁.ϖ ^ (n₁ + 1)) = 0 := by
      have := congrArg (fun x => x - w₀) h
      simpa [hsh_def] using this.symm
    rw [map_pow] at this
    exact pow_ne_zero _ ((Valuation.ne_zero_iff Valued.v).1 ϖ₁.pos.ne') this

  set a : K := pmoebius K₀ (Matrix.ProjGenLinGroup.mk gₐ) wₐ with ha_def
  set z₀ : K := pmoebius K₀ (Matrix.ProjGenLinGroup.mk g₀) w₀ with hz₀_def
  set w : K := pmoebius K₀ (Matrix.ProjGenLinGroup.mk g₀) (sh n₁) with hw_def
  have ha : a ∈ upperHalfPlane K₀ K := pmoebius_mem_upperHalfPlane K₀ hΩₐ _
  have hz₀ : z₀ ∈ upperHalfPlane K₀ K := pmoebius_mem_upperHalfPlane K₀ hΩ₀ _
  have hw : w ∈ upperHalfPlane K₀ K := pmoebius_mem_upperHalfPlane K₀ hΩ₁ _

  have actv : ∀ (γ : G) (gl : GL (Fin 2) K₀), γ • (gl • (LT.LatticeTree.stdVertex R K₀)) = (c γ * gl) • (LT.LatticeTree.stdVertex R K₀) := by
    intro γ gl; rw [hρ γ, ← hc γ, CerednikDrinfeld.BruhatTits.pgl_mk_smul, mul_smul]
  have actp : ∀ (γ : G) (gl : GL (Fin 2) K₀) {x : K}, x ∈ upperHalfPlane K₀ K →
      pmoebius K₀ (ρ γ) (pmoebius K₀ (Matrix.ProjGenLinGroup.mk gl) x) =
        pmoebius K₀ (Matrix.ProjGenLinGroup.mk (c γ * gl)) x := by
    intro γ gl x hx; rw [← hc γ, ← pmoebius_mul K₀ hx, ← map_mul]
  have τc : ∀ (γ : G) (gl : GL (Fin 2) K₀), τ ((c γ * gl) • (LT.LatticeTree.stdVertex R K₀)) = τ (gl • (LT.LatticeTree.stdVertex R K₀)) := by
    intro γ gl; rw [← actv, hτ]

  have guardA : ∀ (γ : G) {x : K}, x ∈ affinoid ϖ₁ 0 →
      pmoebius K₀ (ρ γ) a ≠ pmoebius K₀ (Matrix.ProjGenLinGroup.mk g₀) x := by
    intro γ x hx h
    rw [ha_def, actp γ gₐ hΩₐ] at h
    have hxΩ : x ∈ upperHalfPlane K₀ K := affinoid_subset_upperHalfPlane ϖ₁ 0 hx
    have e := smul_stdVertex_eq_of_mem_affinoid_zero R K₀ ϖ hϖ K hint hv ϖ₁ (c γ * gₐ) g₀
      (x := pmoebius K₀ (Matrix.ProjGenLinGroup.mk g₀) x)
      (by rw [← h, hinv _ hΩₐ]; exact hwₐ) (by rw [hinv _ hxΩ]; exact hx)
    apply hsep
    rw [← e, τc]
  have guardZ : ∀ (γ : G) {x : K}, x ∈ affinoid ϖ₁ 0 →
      pmoebius K₀ (ρ γ) (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g₀) x) ≠ a := by
    intro γ x hx h
    have hxΩ : x ∈ upperHalfPlane K₀ K := affinoid_subset_upperHalfPlane ϖ₁ 0 hx
    rw [ha_def, actp γ g₀ hxΩ] at h
    have e := smul_stdVertex_eq_of_mem_affinoid_zero R K₀ ϖ hϖ K hint hv ϖ₁ (c γ * g₀) gₐ (x := a)
      (by rw [ha_def, ← h, hinv _ hxΩ]; exact hx) (by rw [ha_def, hinv _ hΩₐ]; exact hwₐ)
    apply hsep
    rw [← τc γ g₀, e]
  have hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀ := fun γ => guardA γ hw₀
  have hwa : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ w := fun γ => guardA γ hw₁
  have haz₀ : ∀ γ : G, pmoebius K₀ (ρ γ) z₀ ≠ a := fun γ => guardZ γ hw₀
  have hwz₀ : ∀ γ : G, pmoebius K₀ (ρ γ) z₀ ≠ w := by
    intro γ h

    have hL : pmoebius K₀ (Matrix.ProjGenLinGroup.mk (c γ * g₀)) w₀ = w := by
      rw [← actp γ g₀ hΩ₀]; exact h
    have hx1 : pmoebius K₀ (Matrix.ProjGenLinGroup.mk (c γ * g₀))⁻¹ w ∈ affinoid ϖ₁ 0 := by
      rw [← hL, hinv _ hΩ₀]; exact hw₀
    have hx2 : pmoebius K₀ (Matrix.ProjGenLinGroup.mk g₀)⁻¹ w ∈ affinoid ϖ₁ 0 := by
      rw [hw_def, hinv _ hΩ₁]; exact hw₁
    have hvert := smul_stdVertex_eq_of_mem_affinoid_zero R K₀ ϖ hϖ K hint hv ϖ₁ (c γ * g₀) g₀ hx1 hx2
    have hfix : γ ∈ stabilizer G (g₀ • LT.LatticeTree.stdVertex R K₀) := by
      show γ • (g₀ • LT.LatticeTree.stdVertex R K₀) = g₀ • LT.LatticeTree.stdVertex R K₀
      rw [actv, hvert]

    apply hw₁bad
    refine ⟨⟨γ, hfix⟩, ?_⟩
    show pmoebius K₀ (Matrix.ProjGenLinGroup.mk g₀)⁻¹ (pmoebius K₀ (ρ γ) z₀) = sh n₁
    rw [hz₀_def] at h ⊢
    rw [h, hw_def, hinv _ hΩ₁]

  have hst : {γ : G | ρ γ • (LT.LatticeTree.stdVertex R K₀) = (LT.LatticeTree.stdVertex R K₀)}.Finite := by
    have hf : (stabilizer G (LT.LatticeTree.stdVertex R K₀) : Set G).Finite :=
      Set.toFinite (stabilizer G (LT.LatticeTree.stdVertex R K₀) : Set G)
    refine hf.subset ?_
    intro γ hγ
    simp only [Set.mem_setOf_eq] at hγ
    show γ ∈ stabilizer G (LT.LatticeTree.stdVertex R K₀)
    rw [mem_stabilizer_iff, hρ γ]; exact hγ
  have hdisc := isDiscrete_of_finite_stabilizer_stdVertex R K₀ ϖ hϖ K hint hv hq ρ hst
  have hΘ : ∀ x ∈ upperHalfPlane K₀ K, ∀ y ∈ upperHalfPlane K₀ K, ∀ u ∈ upperHalfPlane K₀ K,
      ∀ z ∈ upperHalfPlane K₀ K, ThetaMultipliable ρ x y u z :=
    fun x hx y hy u hu z hz => thetaMultipliable_of_isDiscrete_of_isExhausted ϖ₁ hex ρ hdisc hx hy hu hz

  obtain ⟨Q', hQ'⟩ := exists_monoidHom_monoidHom_eq_period ρ ha hz₀ hw hz₀a haz₀ hwa hwz₀ hΘ
  have hsym : ∀ α β : G, period ρ a z₀ α β = period ρ a z₀ β α :=
    fun α β => period_symm ρ ha hz₀ hw hz₀a haz₀ hwa hwz₀ hΘ α β

  have hF : ∀ α β : G, (((Q'⁻¹) α β : Kˣ) : K) ∈ Kp := by
    intro α β
    rw [MonoidHom.inv_apply, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, hQ']
    exact Kp.inv_mem (hKp α β)
  obtain ⟨Q, hQ⟩ := MonoidHom.exists_subfield_units_coe_eq Kp Q'⁻¹ hF
  have hQv : ∀ α β : G, (((Q α β : (↥Kp)ˣ) : ↥Kp) : K) = (period ρ a z₀ α β)⁻¹ := by
    intro α β; rw [hQ, MonoidHom.inv_apply, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, hQ']
  have hper0 : ∀ α β : G, period ρ a z₀ α β ≠ 0 := fun α β => by rw [← hQ']; exact (Q' α β).ne_zero
  refine ⟨Q, ?_, ?_, ?_⟩
  · intro α β
    apply Units.ext; apply Subtype.ext
    show (((Q α β : (↥Kp)ˣ) : ↥Kp) : K) = (((Q β α : (↥Kp)ˣ) : ↥Kp) : K)
    rw [hQv, hQv, hsym]
  · intro α β
    rw [hQv, inv_mul_cancel₀ (hper0 α β)]
  · intro α β
    rw [hQv, Valuation.map_inv,
      v_period_eq_zpow_neg_sum_stabWidth_mul_pathCycle_mul_pathCycle R K₀ ϖ hϖ K hint hv hq ϖ₁ ρ hρ hfin τ hτ hadj eE g₀ gₐ hw₀ hwₐ hsep α β,
      zpow_neg, inv_inv]

end S_CerednikDrinfeld_Omega_exists_monoidHom_monoidHom_symm_mul_period_eq_one_v_eq_zpow_stabWidth
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_exists_monoidHom_monoidHom_symm_mul_period_eq_one_v_eq_zpow_stabWidth (solution)
