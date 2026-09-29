-- Prove2me | solution 1 for CerednikDrinfeld.Omega.exists_mk_mem_invariantFieldOf_apply_ne_zero_ordAt_eq_card_stabilizer_of_map_le_typePreserving_of_v_card_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/6bd31359-88d4-584a-9e81-00be317e4b3a

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotientNormalizer
import Definitions.Def_CerednikDrinfeld_OmegaOrdAt
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Theorems.Thm_CerednikDrinfeld_Omega_exists_isThetaPair_ordAt_eq_card
import Theorems.Thm_CerednikDrinfeld_Omega_theta_apply_pmoebius_basePoint_eq_one_of_isOfFinOrder
import Theorems.Thm_CerednikDrinfeld_Omega_exists_eq_prod_theta_forall_ne_pmoebius_of_forall_isOfFinOrder_of_colouring
import Theorems.Thm_CerednikDrinfeld_Omega_isDiscrete_of_finite_stabilizer_stdVertex
import Theorems.Thm_CerednikDrinfeld_Omega_countable_of_isDiscrete
import Theorems.Thm_CerednikDrinfeld_Omega_exists_mem_upperHalfPlane_forall_pmoebius_ne_of_countable_of_archimedean
import Theorems.Thm_CerednikDrinfeld_Omega_exists_monoidHom_fracAct_thetaMer_eq
import Theorems.Thm_CerednikDrinfeld_Omega_thetaMer_eq_mk_of_isThetaPair
import Theorems.Thm_CerednikDrinfeld_Omega_ordAt_mul
import Theorems.Thm_CerednikDrinfeld_Omega_exists_eq_coordSub_pow_ordAt_mul_and_apply_ne_zero
import Theorems.Thm_CerednikDrinfeld_Omega_exists_finset_forall_v_sub_lt_of_finite_residueField
import Theorems.Thm_CerednikDrinfeld_BruhatTits_finite_stabilizer_vertex_of_finite_stabilizer_dart
import Theorems.Thm_CerednikDrinfeld_Omega_exists_eq_coordSub_pow_ordAt_mul_and_apply_ne_zero
import Theorems.Thm_CerednikDrinfeld_BruhatTits_tree_connected_and_colorable_two
import Theorems.Thm_CerednikDrinfeld_Mumford_vertexType_add_one_of_adj_and_vertexType_smul_and_exists_typeCharacter
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_exists_mk_mem_invariantFieldOf_apply_ne_zero_ordAt_eq_card_stabilizer_of_map_le_typePreserving_of_v_card_eq_one
p2m_attr_erase "simp" "LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq CerednikDrinfeld.Mumford.walkOverlap_nil_right CerednikDrinfeld.Mumford.walkOverlap_nil_left LocalGL2.swapUnit_val"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford AlgebraicCurve

theorem ordAt_eq_zero_of_apply_ne_zero'
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    [CompleteSpace K] [IsAlgClosed K]
    (ϖ : Omega.PseudoUniformizer K₀ K) (hex : Omega.IsExhausted ϖ)
    (hfin : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
      ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    (F : ↥(Omega.holRing ϖ)) (z : ↥(Omega.upperHalfPlane K₀ K))
    (hFz : (F : ↥(Omega.upperHalfPlane K₀ K) → K) z ≠ 0) : Omega.ordAt ϖ F z = 0 := by
  have hF : F ≠ 0 := fun h => hFz (by rw [h]; rfl)
  obtain ⟨G, hG, -⟩ := exists_eq_coordSub_pow_ordAt_mul_and_apply_ne_zero K₀ K hrk ϖ hex hfin F hF z
  by_contra hne
  apply hFz
  have := congrArg (fun H : ↥(Omega.holRing ϖ) => (H : ↥(Omega.upperHalfPlane K₀ K) → K) z) hG
  simp only [Subring.coe_mul, Subring.coe_pow, Pi.mul_apply, Pi.pow_apply, coordSub_apply_self,
    zero_pow hne, zero_mul] at this
  exact this

set_option maxHeartbeats 6400000 in
theorem solution

    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)

    (hval : ∀ ε : Γ₀, ε ≠ 0 → ∃ y : K, y ≠ 0 ∧ Valued.v y ≤ ε)
    [CompleteSpace K] [IsAlgClosed K]
    (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀]
    [Finite (IsLocalRing.ResidueField R₀)]
    (hR₀ : ∀ x : K₀, x ∈ Set.range (algebraMap R₀ K₀) ↔ Valued.v (algebraMap K₀ K x) ≤ 1)

    (ϖ : Omega.PseudoUniformizer K₀ K) (ϖ₀ : R₀) (hϖ₀ : Irreducible ϖ₀) (hϖ : algebraMap R₀ K₀ ϖ₀ = ϖ.ϖ)
    (hex : Omega.IsExhausted ϖ)

    (G : Type) [Group G] (ρ : G →* PGL(2, K₀))
    [IsDomain (Omega.HolRingOf ϖ ρ)]

    (Γ : Subgroup G) (htp : Γ.map ρ ≤ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))
    [Mumford.GraphAction ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀)]
    (hfin : ∀ d : (BruhatTits.tree R₀ K₀).Dart, Finite (MulAction.stabilizer (↥(Γ.map ρ)) d))

    (htame : ∀ w : LT.LatticeTree.Vertex R₀ K₀, Valued.v ((Nat.card ↥(MulAction.stabilizer (↥(Γ.map ρ)) w) : ℕ) : K) = 1)
    [Fintype (Mumford.QuotVert ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀))]
    [Fintype (Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀))]
    (z : ↥(Omega.upperHalfPlane K₀ K)) :
    ∃ (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ)),
      Localization.mk g ⟨h, hh⟩ ∈ Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Γ ∧
      (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ K) → K) z ≠ 0 ∧ g ≠ 0 ∧
      Omega.ordAt ϖ (show ↥(Omega.holRing ϖ) from g) z = Nat.card ↥(MulAction.stabilizer ↥(Γ.map ρ) z) := by
  classical

  haveI hdom : IsDomain ↥(Omega.holRing ϖ) := (HolRingOf.isDomain_iff ϖ ρ).1 inferInstance
  have hfinA := exists_finset_forall_v_sub_lt_of_finite_residueField K₀ K R₀ hR₀ ϖ ϖ₀ hϖ₀ hϖ
  let G' : Subgroup PGL(2, K₀) := Γ.map ρ
  let ρ' : ↥G' →* PGL(2, K₀) := G'.subtype

  have hfinG' : ∀ d : (BruhatTits.tree R₀ K₀).Dart, Finite ↥(MulAction.stabilizer ↥G' d) := hfin
  have hfinV : ∀ v : LT.LatticeTree.Vertex R₀ K₀, Finite ↥(MulAction.stabilizer ↥G' v) :=
    BruhatTits.finite_stabilizer_vertex_of_finite_stabilizer_dart R₀ K₀ ↥G' hfinG'
  haveI hfq : Finite (R₀ ⧸ Ideal.span {ϖ₀}) :=
    Finite.of_equiv (IsLocalRing.ResidueField R₀) (Ideal.quotEquivOfEq (Irreducible.maximalIdeal_eq hϖ₀)).toEquiv
  have hint : ∀ a : R₀, Valued.v (algebraMap K₀ K (algebraMap R₀ K₀ a)) ≤ 1 := fun a => (hR₀ _).1 ⟨a, rfl⟩
  have hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R₀ a :=
    fun a ha => RingHom.mem_rangeS.2 ((hR₀ a).2 ha)
  have hq : ∀ ε : Γ₀, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap K₀ K (algebraMap R₀ K₀ ϖ₀)) ^ N ≤ ε := by
    intro ε hε
    obtain ⟨y, hy0, hy⟩ := hval ε hε
    obtain ⟨N, hN⟩ := hrk (algebraMap K₀ K ϖ.ϖ) y ϖ.lt_one hy0
    exact ⟨N, by rw [hϖ]; exact hN.trans hy⟩
  have hst : {σ : ↥G' | ρ' σ • LT.LatticeTree.stdVertex R₀ K₀ = LT.LatticeTree.stdVertex R₀ K₀}.Finite := by
    haveI := hfinV (LT.LatticeTree.stdVertex R₀ K₀)
    have hset : {σ : ↥G' | ρ' σ • LT.LatticeTree.stdVertex R₀ K₀ = LT.LatticeTree.stdVertex R₀ K₀} =
        ((MulAction.stabilizer ↥G' (LT.LatticeTree.stdVertex R₀ K₀) : Subgroup ↥G') : Set ↥G') := by
      ext σ
      rw [Set.mem_setOf_eq, SetLike.mem_coe, MulAction.mem_stabilizer_iff]
      rfl
    rw [hset]
    exact Set.toFinite _
  have hdisc : IsDiscrete K ρ' := isDiscrete_of_finite_stabilizer_stdVertex R₀ K₀ ϖ₀ hϖ₀ K hint hv hq ρ' hst
  haveI hcount : Countable ↥G' := countable_of_isDiscrete ϖ ρ' hdisc

  obtain ⟨b, z₀, hb, hz₀, hzb, hzz₀, hbz₀⟩ :=
    exists_mem_upperHalfPlane_forall_pmoebius_ne_of_countable_of_archimedean K₀ K ϖ hrk ρ' z.2

  obtain ⟨F, H, hFH, hordFH⟩ := exists_isThetaPair_ordAt_eq_card K₀ K ϖ hrk hex hfinA ρ' hdisc z.2 hb hz₀
    (fun σ h0 => hzz₀ σ h0) (fun σ h0 => hbz₀ σ h0)

  obtain ⟨c, hcval, hcact⟩ := exists_monoidHom_fracAct_thetaMer_eq K₀ K ϖ hex ρ' hdisc z.2 hb hz₀
    (fun σ h0 => hzz₀ σ h0) (fun σ h0 => hbz₀ σ h0)
  have hχ : ∀ σ : ↥G', IsOfFinOrder σ → c⁻¹ σ = 1 := by
    intro σ hσ
    rw [MonoidHom.inv_apply, inv_eq_one]
    apply Units.ext
    rw [hcval, Units.val_one]
    exact theta_apply_pmoebius_basePoint_eq_one_of_isOfFinOrder K₀ K ϖ hex ρ' hdisc z.2 hb hz₀
      (fun σ h0 => hzz₀ σ h0) (fun σ h0 => hbz₀ σ h0) σ hσ

  have hJ : ∃ (n : ℕ) (a bb : Fin n → K) (z₁ : K),
      (∀ i, a i ∈ Omega.upperHalfPlane K₀ K) ∧ (∀ i, bb i ∈ Omega.upperHalfPlane K₀ K) ∧ z₁ ∈ Omega.upperHalfPlane K₀ K ∧
      (∀ i (σ : ↥G'), pmoebius K₀ (ρ' σ) (a i) ≠ z₁) ∧ (∀ i (σ : ↥G'), pmoebius K₀ (ρ' σ) (bb i) ≠ z₁) ∧
      (∀ i (σ : ↥G'), a i ≠ pmoebius K₀ (ρ' σ) (z : K) ∧ bb i ≠ pmoebius K₀ (ρ' σ) (z : K)) ∧
      ∀ β : ↥G', ((c⁻¹ β : Kˣ) : K) = ∏ i, theta ρ' (a i) (bb i) z₁ (pmoebius K₀ (ρ' β) z₁) := by
    have hρ' : Mumford.ActsThrough (LT.LatticeTree.Vertex R₀ K₀) ρ' := fun σ w => rfl

    have hcb := BruhatTits.tree_connected_and_colorable_two R₀ K₀
    have hvt := Mumford.vertexType_add_one_of_adj_and_vertexType_smul_and_exists_typeCharacter ↥G'
      (BruhatTits.tree R₀ K₀) hcb.1 hcb.2 (LT.LatticeTree.stdVertex R₀ K₀)
    have hτ : ∀ (σ : ↥G') (w : LT.LatticeTree.Vertex R₀ K₀),
        Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) (σ • w) =
          Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) w :=
      fun σ w => (Mumford.mem_typePreserving_iff _ _ _).1 (htp σ.2) w
    have hadj : ∀ u w : LT.LatticeTree.Vertex R₀ K₀, (BruhatTits.tree R₀ K₀).Adj u w →
        Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) u ≠
          Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) w := by
      intro u w huw h
      have := hvt.1 u w huw
      rw [← h] at this
      exact absurd (by linear_combination (-1 : ZMod 2) * this : (1 : ZMod 2) = 0) (by decide)
    obtain ⟨n, a, bb, z₁, ha, hbb, hz₁, hz₁a, hz₁b, havoid, hprod⟩ :=
      exists_eq_prod_theta_forall_ne_pmoebius_of_forall_isOfFinOrder_of_colouring R₀ K₀ ϖ₀ hϖ₀ K hint hv hq hrk ϖ hex
        ρ' hρ' hfinV _ hτ hadj htame c⁻¹ hχ {z}
    refine ⟨n, a, bb, z₁, ha, hbb, hz₁, hz₁a, hz₁b, fun i σ => ?_, hprod⟩
    exact havoid z (Finset.mem_singleton_self z) i σ
  obtain ⟨n, a, bb, z₁, ha, hbb, hz₁, hz₁a, hz₁b, havoid, hprod⟩ := hJ

  have hpairs : ∀ i : Fin n, ∃ Fi Hi : ↥(Omega.holRing ϖ), IsThetaPair ϖ ρ' (a i) (bb i) z₁ Fi Hi ∧
      ∀ w : ↥(Omega.upperHalfPlane K₀ K),
        Omega.ordAt ϖ Fi w = Nat.card {σ : ↥G' // pmoebius K₀ (ρ' σ) (a i) = (w : K)} ∧
        Omega.ordAt ϖ Hi w = Nat.card {σ : ↥G' // pmoebius K₀ (ρ' σ) (bb i) = (w : K)} :=
    fun i => exists_isThetaPair_ordAt_eq_card K₀ K ϖ hrk hex hfinA ρ' hdisc (ha i) (hbb i) hz₁ (hz₁a i) (hz₁b i)
  choose Fi Hi hFHi hordi using hpairs
  have hci : ∀ i : Fin n, ∃ ci : ↥G' →* Kˣ,
      (∀ β : ↥G', ((ci β : Kˣ) : K) = theta ρ' (a i) (bb i) z₁ (pmoebius K₀ (ρ' β) z₁)) ∧
      ∀ β : ↥G', Mumford.fracAct PGL(2, K₀) ↥(Omega.holRing ϖ) (ρ' β) (thetaMer ϖ ρ' (a i) (bb i) z₁) =
        algebraMap K (merField ϖ) (((ci β)⁻¹ : Kˣ) : K) * thetaMer ϖ ρ' (a i) (bb i) z₁ :=
    fun i => exists_monoidHom_fracAct_thetaMer_eq K₀ K ϖ hex ρ' hdisc (ha i) (hbb i) hz₁ (hz₁a i) (hz₁b i)
  choose ci hcival hciact using hci

  have hinvorb : ∀ (σ : ↥G') {x y : K}, x ∈ Omega.upperHalfPlane K₀ K → pmoebius K₀ (ρ' σ) x = y →
      pmoebius K₀ (ρ' σ⁻¹) y = x := by
    intro σ x y hx hxy
    rw [← hxy, map_inv, ← pmoebius_mul K₀ hx, inv_mul_cancel, pmoebius_one]

  let g₀ : ↥(Omega.holRing ϖ) := F * ∏ i, Fi i
  let h₀ : ↥(Omega.holRing ϖ) := H * ∏ i, Hi i

  have hprodOrd : ∀ (s : Finset (Fin n)) (f : Fin n → ↥(Omega.holRing ϖ)), (∀ i ∈ s, f i ≠ 0) →
      (∏ i ∈ s, f i) ≠ 0 ∧ Omega.ordAt ϖ (∏ i ∈ s, f i) z = ∑ i ∈ s, Omega.ordAt ϖ (f i) z := by
    intro s f hf
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨by simp, ?_⟩
      rw [Finset.prod_empty, Finset.sum_empty]
      exact ordAt_eq_zero_of_apply_ne_zero' K₀ K hrk ϖ hex hfinA 1 z (by simp)
    | insert j s hj ih =>
      obtain ⟨h1, h2⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      have hfj : f j ≠ 0 := hf j (Finset.mem_insert_self j s)
      rw [Finset.prod_insert hj, Finset.sum_insert hj]
      exact ⟨mul_ne_zero hfj h1, by rw [ordAt_mul K₀ K ϖ hrk hex hfinA _ _ hfj h1 z, h2]⟩

  have hF0 : F ≠ 0 := by
    intro h0
    have : (F : ↥(Omega.upperHalfPlane K₀ K) → K) ⟨z₀, hz₀⟩ = 0 := by rw [h0]; rfl
    obtain ⟨σ, hσ⟩ := (hFH.2.2.1 ⟨z₀, hz₀⟩).1 this
    exact hzz₀ σ hσ
  have hFi0 : ∀ i, Fi i ≠ 0 := by
    intro i h0
    have : (Fi i : ↥(Omega.upperHalfPlane K₀ K) → K) ⟨z₁, hz₁⟩ = 0 := by rw [h0]; rfl
    obtain ⟨σ, hσ⟩ := ((hFHi i).2.2.1 ⟨z₁, hz₁⟩).1 this
    exact hz₁a i σ hσ
  have hHz : (H : ↥(Omega.upperHalfPlane K₀ K) → K) z ≠ 0 := by
    intro h0
    obtain ⟨σ, hσ⟩ := (hFH.2.1 z).1 h0
    exact hzb σ hσ
  have hHiz : ∀ i, (Hi i : ↥(Omega.upperHalfPlane K₀ K) → K) z ≠ 0 := by
    intro i h0
    obtain ⟨σ, hσ⟩ := ((hFHi i).2.1 z).1 h0
    exact (havoid i σ⁻¹).2 (hinvorb σ (hbb i) hσ).symm
  have hH0 : H ≠ 0 := nonZeroDivisors.ne_zero hFH.1
  have hHi0 : ∀ i, Hi i ≠ 0 := fun i => nonZeroDivisors.ne_zero (hFHi i).1
  obtain ⟨hPF0, hPFord⟩ := hprodOrd Finset.univ Fi (fun i _ => hFi0 i)
  obtain ⟨hPH0, -⟩ := hprodOrd Finset.univ Hi (fun i _ => hHi0 i)
  have hg0 : g₀ ≠ 0 := mul_ne_zero hF0 hPF0
  have hh0 : h₀ ≠ 0 := mul_ne_zero hH0 hPH0
  have hhnd : h₀ ∈ nonZeroDivisors ↥(Omega.holRing ϖ) := mem_nonZeroDivisors_of_ne_zero hh0
  have hh0z : (h₀ : ↥(Omega.upperHalfPlane K₀ K) → K) z ≠ 0 := by
    show ((H * ∏ i, Hi i : ↥(Omega.holRing ϖ)) : ↥(Omega.upperHalfPlane K₀ K) → K) z ≠ 0
    rw [Subring.coe_mul, SubmonoidClass.coe_finset_prod, Pi.mul_apply, Finset.prod_apply]
    exact mul_ne_zero hHz (Finset.prod_ne_zero_iff.2 fun i _ => hHiz i)

  have hordg : Omega.ordAt ϖ g₀ z = Nat.card ↥(MulAction.stabilizer ↥(Γ.map ρ) z) := by
    show Omega.ordAt ϖ (F * ∏ i, Fi i) z = _
    rw [ordAt_mul K₀ K ϖ hrk hex hfinA _ _ hF0 hPF0 z, hPFord, (hordFH z).1]
    have hzero : ∀ i, Omega.ordAt ϖ (Fi i) z = 0 := by
      intro i
      rw [((hordi i) z).1]
      haveI : IsEmpty {σ : ↥G' // pmoebius K₀ (ρ' σ) (a i) = (z : K)} :=
        ⟨fun σ => (havoid i σ.1⁻¹).1 (hinvorb σ.1 (ha i) σ.2).symm⟩
      exact Nat.card_of_isEmpty
    rw [Finset.sum_eq_zero (fun i _ => hzero i), add_zero]
    refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) fun σ => ?_)
    rw [MulAction.mem_stabilizer_iff, Subtype.ext_iff, Subgroup.smul_def, coe_smul_upperHalfPlane]
    rfl

  let x : merField ϖ := thetaMer ϖ ρ' (z : K) b z₀ * ∏ i, thetaMer ϖ ρ' (a i) (bb i) z₁
  have hfix : ∀ β : ↥G', Mumford.fracAct PGL(2, K₀) ↥(Omega.holRing ϖ) (ρ' β) x = x := by
    intro β
    show Mumford.fracAct PGL(2, K₀) ↥(Omega.holRing ϖ) (ρ' β)
      (thetaMer ϖ ρ' (z : K) b z₀ * ∏ i, thetaMer ϖ ρ' (a i) (bb i) z₁) = _
    rw [map_mul, map_prod, hcact β]
    simp_rw [hciact _ β]
    rw [Finset.prod_mul_distrib, ← map_prod, mul_mul_mul_comm, ← map_mul]

    have hsc : (((c β)⁻¹ : Kˣ) : K) * ∏ i, (((ci i β)⁻¹ : Kˣ) : K) = 1 := by
      have h1 : ∏ i, ((ci i β : Kˣ) : K) = (((c β)⁻¹ : Kˣ) : K) := by
        rw [← MonoidHom.inv_apply, hprod β]
        exact Finset.prod_congr rfl fun i _ => hcival i β
      have h2 : ∏ i, (((ci i β)⁻¹ : Kˣ) : K) = ((c β : Kˣ) : K) := by
        simp_rw [Units.val_inv_eq_inv_val]
        rw [Finset.prod_inv_distrib, h1, Units.val_inv_eq_inv_val, inv_inv]
      rw [h2, Units.val_inv_eq_inv_val, inv_mul_cancel₀ (c β).ne_zero]
    rw [hsc, map_one, one_mul]

  have hact2 : ∀ (γ : G) (y : merField ϖ),
      Mumford.fracAct G (Omega.HolRingOf ϖ ρ) γ y = Mumford.fracAct PGL(2, K₀) ↥(Omega.holRing ϖ) (ρ γ) y := by
    intro γ y
    rfl
  have hmem : x ∈ Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Γ := by
    change ∀ γ : G, γ ∈ Γ → Mumford.fracAct G (Omega.HolRingOf ϖ ρ) γ x = x
    intro γ hγ
    rw [hact2 γ]
    exact hfix ⟨ρ γ, Subgroup.mem_map_of_mem ρ hγ⟩

  have hxeq : (Localization.mk g₀ ⟨h₀, hhnd⟩ : merField ϖ) = x := by
    rw [Localization.mk_eq_mk'_apply, IsLocalization.mk'_eq_iff_eq_mul]
    show algebraMap _ (merField ϖ) (F * ∏ i, Fi i) =
      (thetaMer ϖ ρ' (z : K) b z₀ * ∏ i, thetaMer ϖ ρ' (a i) (bb i) z₁) * algebraMap _ (merField ϖ) (H * ∏ i, Hi i)
    rw [thetaMer_eq_mk_of_isThetaPair ϖ ρ' _ _ _ F H hFH]
    simp_rw [fun i => thetaMer_eq_mk_of_isThetaPair ϖ ρ' _ _ _ (Fi i) (Hi i) (hFHi i)]
    rw [map_mul, map_prod, map_mul, map_prod, mul_mul_mul_comm, ← Finset.prod_mul_distrib]
    congr 1
    · rw [Localization.mk_eq_mk'_apply, IsLocalization.mk'_spec]
    · exact Finset.prod_congr rfl fun i _ => by rw [Localization.mk_eq_mk'_apply, IsLocalization.mk'_spec]
  refine ⟨g₀, h₀, hhnd, ?_, hh0z, hg0, hordg⟩
  show (Localization.mk g₀ ⟨h₀, hhnd⟩ : merField ϖ) ∈ Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Γ
  rw [hxeq]
  exact hmem

end S_CerednikDrinfeld_Omega_exists_mk_mem_invariantFieldOf_apply_ne_zero_ordAt_eq_card_stabilizer_of_map_le_typePreserving_of_v_card_eq_one
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_exists_mk_mem_invariantFieldOf_apply_ne_zero_ordAt_eq_card_stabilizer_of_map_le_typePreserving_of_v_card_eq_one (solution)
