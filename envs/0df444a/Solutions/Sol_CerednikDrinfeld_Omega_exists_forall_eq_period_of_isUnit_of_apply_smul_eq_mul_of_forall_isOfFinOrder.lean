-- Prove2me | solution 1 for CerednikDrinfeld.Omega.exists_forall_eq_period_of_isUnit_of_apply_smul_eq_mul_of_forall_isOfFinOrder
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/2086bf5b-732c-58a5-a38b-b60ce2738c25

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import Definitions.Def_CerednikDrinfeld_ThetaMer
import Theorems.Thm_CerednikDrinfeld_Omega_exists_mem_ribbonKernel_and_v_apply_smul_eq_mul_zpow_stabWidth_of_isUnit_of_forall_isOfFinOrder
import Theorems.Thm_CerednikDrinfeld_Mumford_eq_zero_of_forall_sum_mul_mul_walkCycle_eq_zero
import Theorems.Thm_CerednikDrinfeld_Mumford_surjective_and_apply_eq_zero_iff_mem_closure_stabilizer_of_apply_eq_pathCycle
import Theorems.Thm_CerednikDrinfeld_Mumford_exists_addMonoidHom_abelianization_ribbonKernel_apply_eq_pathCycle
import Theorems.Thm_CerednikDrinfeld_Omega_forall_exists_finset_v_sub_lt_pow_of_finite_quotient
import Theorems.Thm_CerednikDrinfeld_Omega_exists_isUnit_coe_eq_thetaMer_apply_smul_eq_period_mul
import Theorems.Thm_CerednikDrinfeld_Omega_exists_eq_algebraMap_of_isUnit_of_v_apply_eq
import Theorems.Thm_CerednikDrinfeld_Omega_v_period_eq_zpow_neg_sum_stabWidth_mul_pathCycle_mul_pathCycle
import Theorems.Thm_CerednikDrinfeld_Omega_theta_apply_pmoebius_basePoint_eq_one_of_isOfFinOrder
import Theorems.Thm_CerednikDrinfeld_Omega_exists_monoidHom_isAutomorphicWithMultiplier_theta
import Theorems.Thm_CerednikDrinfeld_Omega_isDomain_holRing
import Theorems.Thm_CerednikDrinfeld_Omega_isDiscrete_of_finite_stabilizer_stdVertex
import Theorems.Thm_CerednikDrinfeld_Omega_thetaMultipliable_of_isDiscrete_of_isExhausted
import Theorems.Thm_CerednikDrinfeld_BruhatTits_tree_isTree
import Theorems.Thm_CerednikDrinfeld_BruhatTits_finite_quotEdge_of_finite_quotVert
import Theorems.Thm_CerednikDrinfeld_Omega_smul_stdVertex_eq_of_mem_affinoid_zero
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.GroupTheory.OrderOfElement
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_exists_forall_eq_period_of_isUnit_of_apply_smul_eq_mul_of_forall_isOfFinOrder
p2m_attr_erase "simp" "LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq CerednikDrinfeld.Mumford.walkOverlap_nil_right CerednikDrinfeld.Mumford.walkOverlap_nil_left LocalGL2.swapUnit_val"

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford MulAction

namespace Law3UAPW
theorem walkCycle_copy {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
    [DecidableEq (QuotEdge G 𝒯)] {E : Type} (orb : E → QuotEdge G 𝒯) {u v u' v' : W} (p : 𝒯.Walk u v)
    (hu : u = u') (hv : v = v') : walkCycle 𝒯 orb (p.copy hu hv) = walkCycle 𝒯 orb p := by
  subst hu hv; rfl
end Law3UAPW

theorem solution
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (hq : ∀ ε : Γ₀, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ N ≤ ε)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (ϖ₁ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ₁)
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀))
    [MulAction G (LT.LatticeTree.Vertex R K₀)]
    [CerednikDrinfeld.Mumford.GraphAction G (CerednikDrinfeld.BruhatTits.tree R K₀)]
    (hρ : CerednikDrinfeld.Mumford.ActsThrough (LT.LatticeTree.Vertex R K₀) ρ)
    (hρinj : Function.Injective ρ)
    (hfin : ∀ w : LT.LatticeTree.Vertex R K₀, Finite (MulAction.stabilizer G w))
    [Finite (CerednikDrinfeld.Mumford.QuotVert G (LT.LatticeTree.Vertex R K₀))]
    (τ : LT.LatticeTree.Vertex R K₀ → ZMod 2) (hτ : ∀ (g : G) (w : LT.LatticeTree.Vertex R K₀), τ (g • w) = τ w)
    (hadj : ∀ u w : LT.LatticeTree.Vertex R K₀, (CerednikDrinfeld.BruhatTits.tree R K₀).Adj u w → τ u ≠ τ w)
    (g₀ gₐ : GL (Fin 2) K₀) {w₀ wₐ : K} (hw₀ : w₀ ∈ affinoid ϖ₁ 0) (hwₐ : wₐ ∈ affinoid ϖ₁ 0)
    (hsep : τ (g₀ • LT.LatticeTree.stdVertex R K₀) ≠ τ (gₐ • LT.LatticeTree.stdVertex R K₀))
    (f : ↥(holRing ϖ₁)) (hf : IsUnit f) (χ : G →* Kˣ)
    (haut : ∀ (γ : G) (z : ↥(upperHalfPlane K₀ K)),
      (f : ↥(upperHalfPlane K₀ K) → K) ((ρ γ) • z) = ((χ γ : Kˣ) : K) * (f : ↥(upperHalfPlane K₀ K) → K) z)
    (hχ : ∀ γ : G, IsOfFinOrder γ → χ γ = 1)
    (htame : ∀ w : LT.LatticeTree.Vertex R K₀, Valued.v ((Nat.card ↥(MulAction.stabilizer G w) : ℕ) : K) = 1) :
    ∃ α : G, ∀ β : G,
      ((χ β : Kˣ) : K) = period ρ (pmoebius K₀ (Matrix.ProjGenLinGroup.mk gₐ) wₐ) (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g₀) w₀) α β := by
  classical

  have hinjK : Function.Injective (algebraMap K₀ K) := (algebraMap K₀ K).injective
  have hinjR : Function.Injective (algebraMap R K₀) := IsFractionRing.injective R K₀
  set q : Γ₀ := Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) with hq_def
  have hq0 : q ≠ 0 := by
    rw [hq_def, ne_eq, Valuation.zero_iff, map_eq_zero_iff _ hinjK, map_eq_zero_iff _ hinjR]; exact hϖ.ne_zero
  have hTree := CerednikDrinfeld.BruhatTits.tree_isTree R K₀
  have hΩₐ : wₐ ∈ upperHalfPlane K₀ K := affinoid_subset_upperHalfPlane ϖ₁ 0 hwₐ
  have hΩ₀ : w₀ ∈ upperHalfPlane K₀ K := affinoid_subset_upperHalfPlane ϖ₁ 0 hw₀
  set a : K := pmoebius K₀ (Matrix.ProjGenLinGroup.mk gₐ) wₐ with ha_def
  set z₀ : K := pmoebius K₀ (Matrix.ProjGenLinGroup.mk g₀) w₀ with hz₀_def
  have ha : a ∈ upperHalfPlane K₀ K := pmoebius_mem_upperHalfPlane K₀ hΩₐ _
  have hz₀ : z₀ ∈ upperHalfPlane K₀ K := pmoebius_mem_upperHalfPlane K₀ hΩ₀ _
  choose cl hcl using fun γ : G => Matrix.ProjGenLinGroup.mk_surjective (ρ γ)
  have actv : ∀ (γ : G) (gl : GL (Fin 2) K₀),
      γ • (gl • (LT.LatticeTree.stdVertex R K₀)) = (cl γ * gl) • (LT.LatticeTree.stdVertex R K₀) := by
    intro γ gl; rw [hρ γ, ← hcl γ, CerednikDrinfeld.BruhatTits.pgl_mk_smul, mul_smul]
  have actp : ∀ (γ : G) (gl : GL (Fin 2) K₀) {x : K}, x ∈ upperHalfPlane K₀ K →
      pmoebius K₀ (ρ γ) (pmoebius K₀ (Matrix.ProjGenLinGroup.mk gl) x) =
        pmoebius K₀ (Matrix.ProjGenLinGroup.mk (cl γ * gl)) x := by
    intro γ gl x hx; rw [← hcl γ, ← pmoebius_mul K₀ hx, ← map_mul]
  have τc : ∀ (γ : G) (gl : GL (Fin 2) K₀), τ ((cl γ * gl) • (LT.LatticeTree.stdVertex R K₀)) = τ (gl • (LT.LatticeTree.stdVertex R K₀)) := by
    intro γ gl; rw [← actv, hτ]
  have hinv : ∀ (p : PGL(2, K₀)) {y : K}, y ∈ upperHalfPlane K₀ K → pmoebius K₀ p⁻¹ (pmoebius K₀ p y) = y := by
    intro p y hy; rw [← pmoebius_mul K₀ hy, inv_mul_cancel]; simp [pmoebius]
  have hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀ := by
    intro γ h
    rw [ha_def, actp γ gₐ hΩₐ] at h
    have e := smul_stdVertex_eq_of_mem_affinoid_zero R K₀ ϖ hϖ K hint hv ϖ₁ (cl γ * gₐ) g₀ (x := z₀)
      (by rw [← h, hinv _ hΩₐ]; exact hwₐ) (by rw [hz₀_def, hinv _ hΩ₀]; exact hw₀)
    apply hsep; rw [← e, τc]
  have hst : {γ : G | ρ γ • (LT.LatticeTree.stdVertex R K₀) = (LT.LatticeTree.stdVertex R K₀)}.Finite := by
    haveI : Finite (stabilizer G (LT.LatticeTree.stdVertex R K₀)) := hfin _
    refine (Set.toFinite ((stabilizer G (LT.LatticeTree.stdVertex R K₀) : Subgroup G) : Set G)).subset ?_
    intro γ hγ
    simp only [Set.mem_setOf_eq] at hγ
    show γ ∈ stabilizer G (LT.LatticeTree.stdVertex R K₀)
    rw [mem_stabilizer_iff, hρ γ]; exact hγ
  have hdisc := isDiscrete_of_finite_stabilizer_stdVertex R K₀ ϖ hϖ K hint hv hq ρ hst
  have hΘ : ∀ x ∈ upperHalfPlane K₀ K, ∀ y ∈ upperHalfPlane K₀ K, ∀ u ∈ upperHalfPlane K₀ K,
      ∀ w ∈ upperHalfPlane K₀ K, ThetaMultipliable ρ x y u w :=
    fun x hx y hy u hu w hw => thetaMultipliable_of_isDiscrete_of_isExhausted ϖ₁ hex ρ hdisc hx hy hu hw
  have hfinK := forall_exists_finset_v_sub_lt_pow_of_finite_quotient R K₀ ϖ hϖ K hint hv hq ϖ₁
  haveI : IsDomain ↥(holRing ϖ₁) := isDomain_holRing K₀ K ϖ₁ hrk hex hfinK

  haveI hQE : Finite (QuotEdge G (CerednikDrinfeld.BruhatTits.tree R K₀)) :=
    CerednikDrinfeld.BruhatTits.finite_quotEdge_of_finite_quotVert R K₀ ϖ hϖ
  let E : Type := {e : QuotEdge G (CerednikDrinfeld.BruhatTits.tree R K₀) // τ e.out.fst = 0}
  haveI : Fintype E := Fintype.ofFinite E
  let eE : E ≃ {e : QuotEdge G (CerednikDrinfeld.BruhatTits.tree R K₀) // τ e.out.fst = 0} := Equiv.refl _
  let Dw : DegeneracyData E (QuotVert G (LT.LatticeTree.Vertex R K₀)) :=
    ⟨fun e => Quotient.mk (orbitRel G (LT.LatticeTree.Vertex R K₀)) (eE e).1.out.fst,
     fun e => Quotient.mk (orbitRel G (LT.LatticeTree.Vertex R K₀)) (eE e).1.out.snd,
     fun _ => 1⟩

  obtain ⟨cf, hcfZ, hflowf, -⟩ :=
    exists_mem_ribbonKernel_and_v_apply_smul_eq_mul_zpow_stabWidth_of_isUnit_of_forall_isOfFinOrder R K₀ ϖ hϖ K
      hint hv hq hrk ϖ₁ hex ρ hρ hρinj hfin τ hτ hadj eE f hf χ haut hχ htame

  obtain ⟨Φ, hΦ⟩ := exists_addMonoidHom_abelianization_ribbonKernel_apply_eq_pathCycle (CerednikDrinfeld.BruhatTits.tree R K₀) hTree τ hτ hadj
    Dw eE (Equiv.refl _) (fun _ => rfl) (fun _ => rfl) (LT.LatticeTree.stdVertex R K₀)
  obtain ⟨hsurj, -⟩ := surjective_and_apply_eq_zero_iff_mem_closure_stabilizer_of_apply_eq_pathCycle (CerednikDrinfeld.BruhatTits.tree R K₀) hTree
    τ hτ hadj Dw eE (Equiv.refl _) (fun _ => rfl) (fun _ => rfl) (LT.LatticeTree.stdVertex R K₀) Φ hΦ
  obtain ⟨x, hx⟩ := hsurj (-⟨cf, hcfZ⟩)
  obtain ⟨α, hα⟩ : ∃ α : G, Additive.ofMul (Abelianization.of α) = x := by
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
    exact ⟨g, by change Additive.ofMul (QuotientGroup.mk g) = x; rw [hg]; exact Additive.ofMul.apply_symm_apply x⟩
  have hcyc : pathCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e => (eE e).1) (LT.LatticeTree.stdVertex R K₀) α = -cf := by
    rw [← hΦ α, hα, hx]; rfl

  obtain ⟨U, hUunit, -, hUtheta, hUaut⟩ :=
    exists_isUnit_coe_eq_thetaMer_apply_smul_eq_period_mul K₀ K ϖ₁ hex ρ hdisc ha hz₀ hz₀a α

  have hΘa : ∀ z ∈ upperHalfPlane K₀ K, ThetaMultipliable ρ a (pmoebius K₀ (ρ α) a) z₀ z :=
    fun z hz => hΘ a ha _ (pmoebius_mem_upperHalfPlane K₀ ha _) z₀ hz₀ z hz
  have hz₀αa : ∀ γ : G, pmoebius K₀ (ρ γ) (pmoebius K₀ (ρ α) a) ≠ z₀ := fun γ h =>
    hz₀a (γ * α) (by rw [map_mul, pmoebius_mul K₀ ha]; exact h)
  obtain ⟨cα, hcα, -⟩ := exists_monoidHom_isAutomorphicWithMultiplier_theta ρ ha
    (pmoebius_mem_upperHalfPlane K₀ ha (ρ α)) hz₀ hz₀a hz₀αa hΘa
  have hcα_per : ∀ β : G, ((cα β : Kˣ) : K) = period ρ a z₀ α β := fun β => by rw [hcα β]; rfl
  have hcα_fin : ∀ γ : G, IsOfFinOrder γ → cα γ = 1 := by
    intro γ hγ
    apply Units.ext
    rw [hcα γ, Units.val_one]
    exact theta_apply_pmoebius_basePoint_eq_one_of_isOfFinOrder K₀ K ϖ₁ hex ρ hdisc ha
      (pmoebius_mem_upperHalfPlane K₀ ha (ρ α)) hz₀ hz₀a hz₀αa γ hγ

  set Ui : ↥(holRing ϖ₁) := ((hUunit.unit⁻¹ : (↥(holRing ϖ₁))ˣ) : ↥(holRing ϖ₁)) with hUi_def
  have hUUi : U * Ui = 1 := by rw [hUi_def]; exact hUunit.unit.mul_inv
  have hUival : ∀ z : ↥(upperHalfPlane K₀ K),
      (U : ↥(upperHalfPlane K₀ K) → K) z * (Ui : ↥(upperHalfPlane K₀ K) → K) z = 1 := by
    intro z
    have := congrArg (fun F : ↥(holRing ϖ₁) => (F : ↥(upperHalfPlane K₀ K) → K) z) hUUi
    simpa using this
  have hUne : ∀ z : ↥(upperHalfPlane K₀ K), (U : ↥(upperHalfPlane K₀ K) → K) z ≠ 0 := fun z h0 => by
    have := hUival z; rw [h0, zero_mul] at this; exact zero_ne_one this
  have hUiaut : ∀ (γ : G) (z : ↥(upperHalfPlane K₀ K)),
      (Ui : ↥(upperHalfPlane K₀ K) → K) ((ρ γ) • z) =
        (((cα γ)⁻¹ : Kˣ) : K) * (Ui : ↥(upperHalfPlane K₀ K) → K) z := by
    intro γ z
    have h1 := hUival ((ρ γ) • z)
    have h2 := hUival z
    rw [hUaut γ z, ← hcα_per] at h1

    have hc0 : ((cα γ : Kˣ) : K) ≠ 0 := (cα γ).ne_zero
    field_simp
    rw [Units.val_inv_eq_inv_val]
    field_simp
    linear_combination (Ui : ↥(upperHalfPlane K₀ K) → K) z * h1 - (Ui : ↥(upperHalfPlane K₀ K) → K) ((ρ γ) • z) * ((cα γ : Kˣ) : K) * h2
  set g : ↥(holRing ϖ₁) := f * Ui with hg_def
  have hgunit : IsUnit g := hf.mul (hUunit.unit⁻¹).isUnit
  have hgaut : ∀ (γ : G) (z : ↥(upperHalfPlane K₀ K)),
      (g : ↥(upperHalfPlane K₀ K) → K) ((ρ γ) • z) = (((χ * cα⁻¹) γ : Kˣ) : K) * (g : ↥(upperHalfPlane K₀ K) → K) z := by
    intro γ z
    show (f : ↥(upperHalfPlane K₀ K) → K) ((ρ γ) • z) * (Ui : ↥(upperHalfPlane K₀ K) → K) ((ρ γ) • z) = _
    rw [haut γ z, hUiaut γ z, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul]
    show _ = _ * ((f : ↥(upperHalfPlane K₀ K) → K) z * (Ui : ↥(upperHalfPlane K₀ K) → K) z)
    ring
  have hgχ : ∀ γ : G, IsOfFinOrder γ → (χ * cα⁻¹) γ = 1 := fun γ hγ => by
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hχ γ hγ, hcα_fin γ hγ, inv_one, one_mul]

  obtain ⟨cg, -, hflowg, hconst0⟩ :=
    exists_mem_ribbonKernel_and_v_apply_smul_eq_mul_zpow_stabWidth_of_isUnit_of_forall_isOfFinOrder R K₀ ϖ hϖ K
      hint hv hq hrk ϖ₁ hex ρ hρ hρinj hfin τ hτ hadj eE g hgunit (χ * cα⁻¹) hgaut hgχ htame

  have hUaut' : ∀ (γ : G) (z : ↥(upperHalfPlane K₀ K)),
      (U : ↥(upperHalfPlane K₀ K) → K) ((ρ γ) • z) = ((cα γ : Kˣ) : K) * (U : ↥(upperHalfPlane K₀ K) → K) z := by
    intro γ z; rw [hcα_per]; exact hUaut γ z
  obtain ⟨cU, hcUZ, hflowU0, -⟩ :=
    exists_mem_ribbonKernel_and_v_apply_smul_eq_mul_zpow_stabWidth_of_isUnit_of_forall_isOfFinOrder R K₀ ϖ hϖ K
      hint hv hq hrk ϖ₁ hex ρ hρ hρinj hfin τ hτ hadj eE U hUunit cα hUaut' hcα_fin htame
  have hq1 : q < 1 := by
    refine lt_of_le_of_ne (hint ϖ) ?_
    intro h1
    apply hϖ.not_isUnit
    have hinv' : Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)⁻¹) ≤ 1 := by
      rw [map_inv₀, Valuation.map_inv, ← hq_def, h1, inv_one]
    obtain ⟨a', ha'⟩ := hv _ hinv'
    have hϖ0 : algebraMap R K₀ ϖ ≠ 0 := fun h => hϖ.ne_zero (hinjR (by rw [h, map_zero]))
    have hmul : a' * ϖ = 1 := hinjR (by rw [map_mul, ha', map_one, inv_mul_cancel₀ hϖ0])
    exact ⟨⟨ϖ, a', (mul_comm ϖ a').trans hmul, hmul⟩, rfl⟩
  have hzinj : Function.Injective fun n : ℤ => q ^ n := (zpow_right_strictAnti₀ (zero_lt_iff.2 hq0) hq1).injective

  set d : E → ℤ := fun e => cU e + pathCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e => (eE e).1) (LT.LatticeTree.stdVertex R K₀) α e with hd
  have hpair : ∀ β : G, ∑ e, ((CerednikDrinfeld.Mumford.stabWidth G (CerednikDrinfeld.BruhatTits.tree R K₀) (eE e).1 : ℕ) : ℤ) * d e *
      pathCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e => (eE e).1) (LT.LatticeTree.stdVertex R K₀) β e = 0 := by
    intro β
    have hW2 := v_period_eq_zpow_neg_sum_stabWidth_mul_pathCycle_mul_pathCycle R K₀ ϖ hϖ K hint hv hq ϖ₁ ρ hρ hfin
      τ hτ hadj eE g₀ gₐ hw₀ hwₐ hsep α β
    have hreach : (CerednikDrinfeld.BruhatTits.tree R K₀).Reachable (LT.LatticeTree.stdVertex R K₀) (β • (LT.LatticeTree.stdVertex R K₀)) := hTree.connected.preconnected _ _
    have hpc : pathCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e => (eE e).1) (LT.LatticeTree.stdVertex R K₀) β =
        walkCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e => (eE e).1) (somePath hreach).1 :=
      pathCycle_eq_walkCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e => (eE e).1) hTree.isAcyclic _ β (somePath hreach)
    have hβv : β • (LT.LatticeTree.stdVertex R K₀) = cl β • (LT.LatticeTree.stdVertex R K₀) := by
      have := actv β 1; rw [one_smul, mul_one] at this; exact this
    have L := hflowU0 (cl β) ((somePath hreach).1.copy rfl hβv) w₀ w₀ hw₀ hw₀
    have hcopy : walkCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e => (eE e).1) ((somePath hreach).1.copy rfl hβv) =
        walkCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e => (eE e).1) (somePath hreach).1 := by
      exact Law3UAPW.walkCycle_copy _ _ _ rfl hβv
    rw [hcopy, ← hpc] at L
    have hpt : ((Matrix.ProjGenLinGroup.mk (cl β)) • (⟨w₀, affinoid_subset_upperHalfPlane ϖ₁ 0 hw₀⟩ : ↥(upperHalfPlane K₀ K))) =
        (ρ β) • ⟨w₀, affinoid_subset_upperHalfPlane ϖ₁ 0 hw₀⟩ := by rw [hcl β]
    rw [hpt, hUaut' β, Valuation.map_mul, hcα_per] at L
    have hU0 := (Valuation.ne_zero_iff Valued.v).2 (hUne ⟨w₀, affinoid_subset_upperHalfPlane ϖ₁ 0 hw₀⟩)
    have L' := mul_right_cancel₀ hU0 (L.trans (mul_comm _ _))

    rw [show period ρ a z₀ α β = _ from rfl, hW2] at L'
    have := hzinj L'
    rw [hd]
    simp only [mul_add, add_mul, Finset.sum_add_distrib]
    linarith [this]
  have hdZ : d ∈ ribbonKernel Dw := by
    have h2 := (Φ (Additive.ofMul (Abelianization.of α))).2
    rw [hΦ α] at h2
    exact Submodule.add_mem _ hcUZ h2
  have hd0 : d = 0 := by
    obtain ⟨x', hx'⟩ := hsurj ⟨d, hdZ⟩
    obtain ⟨β, hβ⟩ : ∃ β : G, Additive.ofMul (Abelianization.of β) = x' := by
      obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (Additive.toMul x')
      exact ⟨g, by change Additive.ofMul (QuotientGroup.mk g) = x'; rw [hg]; exact Additive.ofMul.apply_symm_apply x'⟩
    have hcβ : pathCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e => (eE e).1) (LT.LatticeTree.stdVertex R K₀) β = d := by
      rw [← hΦ β, hβ, hx']
    have hsq := hpair β
    rw [hcβ] at hsq
    funext e
    have hnn : ∀ e ∈ Finset.univ, 0 ≤ ((CerednikDrinfeld.Mumford.stabWidth G (CerednikDrinfeld.BruhatTits.tree R K₀) (eE e).1 : ℕ) : ℤ) * d e * d e :=
      fun e _ => by rw [mul_assoc]; exact mul_nonneg (by positivity) (mul_self_nonneg _)
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsq e (Finset.mem_univ e)
    rw [mul_assoc] at this
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (by exact_mod_cast (CerednikDrinfeld.Mumford.stabWidth G (CerednikDrinfeld.BruhatTits.tree R K₀) (eE e).1).ne_zero)
    · exact mul_self_eq_zero.1 h
  have hcUeq : cU = -pathCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e => (eE e).1) (LT.LatticeTree.stdVertex R K₀) α := by
    funext e; have := congrFun hd0 e; simp only [hd, Pi.zero_apply] at this; rw [Pi.neg_apply]; linarith
  have hflowU : ∀ (gg : GL (Fin 2) K₀)
      (p : (CerednikDrinfeld.BruhatTits.tree R K₀).Walk (LT.LatticeTree.stdVertex R K₀) (gg • (LT.LatticeTree.stdVertex R K₀)))
      (w w' : K) (hw : w ∈ affinoid ϖ₁ 0) (hw' : w' ∈ affinoid ϖ₁ 0),
      Valued.v ((U : ↥(upperHalfPlane K₀ K) → K)
          ((Matrix.ProjGenLinGroup.mk gg) • ⟨w, affinoid_subset_upperHalfPlane ϖ₁ 0 hw⟩)) *
        q ^ (∑ e, ((CerednikDrinfeld.Mumford.stabWidth G (CerednikDrinfeld.BruhatTits.tree R K₀) (eE e).1 : ℕ) : ℤ) *
              pathCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e => (eE e).1) (LT.LatticeTree.stdVertex R K₀) α e *
              walkCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e => (eE e).1) p e) =
      Valued.v ((U : ↥(upperHalfPlane K₀ K) → K) ⟨w', affinoid_subset_upperHalfPlane ϖ₁ 0 hw'⟩) := by
    intro gg p w w' hw hw'
    rw [hflowU0 gg p w w' hw hw', hcUeq, mul_assoc, ← zpow_add₀ hq0]
    have : (∑ e, ((CerednikDrinfeld.Mumford.stabWidth G (CerednikDrinfeld.BruhatTits.tree R K₀) (eE e).1 : ℕ) : ℤ) *
          (-pathCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e => (eE e).1) (LT.LatticeTree.stdVertex R K₀) α) e *
          walkCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e => (eE e).1) p e) +
        (∑ e, ((CerednikDrinfeld.Mumford.stabWidth G (CerednikDrinfeld.BruhatTits.tree R K₀) (eE e).1 : ℕ) : ℤ) *
          pathCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e => (eE e).1) (LT.LatticeTree.stdVertex R K₀) α e *
          walkCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e => (eE e).1) p e) = 0 := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_eq_zero fun e _ => by rw [Pi.neg_apply]; ring
    rw [this, zpow_zero, mul_one]

  have hcg0 : cg = 0 := by
    refine eq_zero_of_forall_sum_mul_mul_walkCycle_eq_zero R K₀ τ hτ hadj eE
      (fun e => ((CerednikDrinfeld.Mumford.stabWidth G (CerednikDrinfeld.BruhatTits.tree R K₀) (eE e).1 : ℕ) : ℤ))
      (fun e => by beta_reduce; exact_mod_cast (CerednikDrinfeld.Mumford.stabWidth G (CerednikDrinfeld.BruhatTits.tree R K₀) (eE e).1).ne_zero) cg ?_
    intro gg p
    set P : ↥(upperHalfPlane K₀ K) := (Matrix.ProjGenLinGroup.mk gg) • ⟨w₀, affinoid_subset_upperHalfPlane ϖ₁ 0 hw₀⟩ with hP
    set O : ↥(upperHalfPlane K₀ K) := ⟨w₀, affinoid_subset_upperHalfPlane ϖ₁ 0 hw₀⟩ with hO
    have ef := hflowf gg p w₀ w₀ hw₀ hw₀
    have eg := hflowg gg p w₀ w₀ hw₀ hw₀
    have eU := hflowU gg p w₀ w₀ hw₀ hw₀

    have gval : ∀ z : ↥(upperHalfPlane K₀ K), Valued.v ((g : ↥(upperHalfPlane K₀ K) → K) z) =
        Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) z) * (Valued.v ((U : ↥(upperHalfPlane K₀ K) → K) z))⁻¹ := by
      intro z
      have hUi : (Ui : ↥(upperHalfPlane K₀ K) → K) z = ((U : ↥(upperHalfPlane K₀ K) → K) z)⁻¹ := by
        rw [← mul_eq_one_iff_eq_inv₀ (hUne z), mul_comm]; exact hUival z
      show Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) z * (Ui : ↥(upperHalfPlane K₀ K) → K) z) = _
      rw [Valuation.map_mul, hUi, Valuation.map_inv]
    set Sg : ℤ := ∑ e, ((CerednikDrinfeld.Mumford.stabWidth G (CerednikDrinfeld.BruhatTits.tree R K₀) (eE e).1 : ℕ) : ℤ) * cg e *
        walkCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e => (eE e).1) p e with hSg
    set Sf : ℤ := ∑ e, ((CerednikDrinfeld.Mumford.stabWidth G (CerednikDrinfeld.BruhatTits.tree R K₀) (eE e).1 : ℕ) : ℤ) * cf e *
        walkCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e => (eE e).1) p e with hSf
    set Sa : ℤ := ∑ e, ((CerednikDrinfeld.Mumford.stabWidth G (CerednikDrinfeld.BruhatTits.tree R K₀) (eE e).1 : ℕ) : ℤ) *
        pathCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e => (eE e).1) (LT.LatticeTree.stdVertex R K₀) α e *
        walkCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e => (eE e).1) p e with hSa
    have hSfa : Sf + Sa = 0 := by
      rw [hSf, hSa, ← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun e _ => ?_
      rw [hcyc, Pi.neg_apply]; ring

    have hvU0 : ∀ z, Valued.v ((U : ↥(upperHalfPlane K₀ K) → K) z) ≠ 0 := fun z => (Valuation.ne_zero_iff _).2 (hUne z)
    have hfval : ∀ z : ↥(upperHalfPlane K₀ K), (f : ↥(upperHalfPlane K₀ K) → K) z ≠ 0 := by
      obtain ⟨f', hf'⟩ := hf.exists_right_inv
      intro z h0
      have h1 := congrArg (fun F : ↥(holRing ϖ₁) => (F : ↥(upperHalfPlane K₀ K) → K) z) hf'
      have h2 : (f : ↥(upperHalfPlane K₀ K) → K) z * (f' : ↥(upperHalfPlane K₀ K) → K) z = 1 := by simpa using h1
      rw [h0, zero_mul] at h2; exact zero_ne_one h2
    have hvf0 : ∀ z, Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) z) ≠ 0 := fun z => (Valuation.ne_zero_iff _).2 (hfval z)
    have key : q ^ Sg = 1 := by
      have e1 := eg
      rw [gval, gval, ef] at e1
      have eU' : Valued.v ((U : ↥(upperHalfPlane K₀ K) → K) P) = Valued.v ((U : ↥(upperHalfPlane K₀ K) → K) O) * (q ^ Sa)⁻¹ := by
        rw [← eU, mul_assoc, mul_inv_cancel₀ (zpow_ne_zero _ hq0), mul_one]
      rw [eU'] at e1
      have hAB : Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) O) * (Valued.v ((U : ↥(upperHalfPlane K₀ K) → K) O))⁻¹ ≠ 0 :=
        mul_ne_zero (hvf0 O) (inv_ne_zero (hvU0 O))
      have e2 : Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) O) * (Valued.v ((U : ↥(upperHalfPlane K₀ K) → K) O))⁻¹ * (q ^ Sf * q ^ Sa) =
          Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) O) * (Valued.v ((U : ↥(upperHalfPlane K₀ K) → K) O))⁻¹ * q ^ Sg := by
        calc _ = Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) O) * q ^ Sf *
              (Valued.v ((U : ↥(upperHalfPlane K₀ K) → K) O) * (q ^ Sa)⁻¹)⁻¹ := by rw [mul_inv, inv_inv]; ac_rfl
          _ = _ := e1
      have e3 := mul_left_cancel₀ hAB e2
      rw [← zpow_add₀ hq0, hSfa, zpow_zero] at e3
      exact e3.symm
    exact (zpow_right_strictAnti₀ (zero_lt_iff.2 hq0) hq1).injective (by rw [key, zpow_zero])

  have hvg := hconst0 hcg0
  obtain ⟨c₀, hc₀⟩ := exists_eq_algebraMap_of_isUnit_of_v_apply_eq K₀ K ϖ₁ hrk hex hfinK g hgunit hvg
  have hgconst : ∀ z : ↥(upperHalfPlane K₀ K), (g : ↥(upperHalfPlane K₀ K) → K) z = c₀ := by
    intro z; rw [hc₀]; rfl
  have hc00 : c₀ ≠ 0 := by
    intro h0; apply hgunit.ne_zero; rw [hc₀, h0, map_zero]

  have htriv : ∀ β : G, ((χ β : Kˣ) : K) * (((cα β)⁻¹ : Kˣ) : K) = 1 := by
    intro β
    have := hgaut β ⟨z₀, hz₀⟩
    rw [hgconst, hgconst, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul] at this
    exact (mul_right_cancel₀ hc00 (this.symm.trans (one_mul c₀).symm))
  refine ⟨α, fun β => ?_⟩
  rw [← hcα_per β]
  have := htriv β
  rwa [Units.val_inv_eq_inv_val, mul_inv_eq_one₀ (cα β).ne_zero] at this

end S_CerednikDrinfeld_Omega_exists_forall_eq_period_of_isUnit_of_apply_smul_eq_mul_of_forall_isOfFinOrder
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_exists_forall_eq_period_of_isUnit_of_apply_smul_eq_mul_of_forall_isOfFinOrder (solution)
