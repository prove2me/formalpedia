-- Prove2me | solution 1 for CerednikDrinfeld.Mumford.finiteHom_degTotal_eq_index_of_mumfordQuotient_conj
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/889bc299-04d6-55f8-9ff2-77556b8f8992

import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Definitions.Def_AlgebraicCurve_TotallyDegenerateCovering_Hom
import Mathlib.GroupTheory.Index

import Mathlib
import Theorems.Thm_CerednikDrinfeld_Mumford_exists_presentation_conj_apply_eq_of_apply_eq_pathCycle
import Theorems.Thm_CerednikDrinfeld_Mumford_exists_addMonoidHom_abelianization_ribbonKernel_apply_eq_pathCycle
import Theorems.Thm_CerednikDrinfeld_BruhatTits_tree_isTree
import Theorems.Thm_CerednikDrinfeld_BruhatTits_tree_connected_and_colorable_two
import Theorems.Thm_CerednikDrinfeld_Mumford_vertexType_add_one_of_adj_and_vertexType_smul_and_exists_typeCharacter
import Theorems.Thm_CerednikDrinfeld_BruhatTits_finite_stabilizer_vertex_of_finite_stabilizer_dart
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Mumford_finiteHom_degTotal_eq_index_of_mumfordQuotient_conj
p2m_attr_erase "simp" "LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq"

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Mumford

namespace Skel

theorem graphAction_subgroup {P : Type} [Group P] {W : Type} [MulAction P W] (𝒯 : SimpleGraph W)
    [Mumford.GraphAction P 𝒯] (S : Subgroup P) : Mumford.GraphAction ↥S 𝒯 :=
  ⟨fun g _ _ h => Mumford.GraphAction.smul_adj (g : P) h⟩
end Skel

section
open MulAction
namespace Skel

theorem card_stabilizer_inv_smul_eq {P : Type} [Group P] {W : Type} [MulAction P W] (𝒯 : SimpleGraph W)
    [GraphAction P 𝒯] (H G₂ : Subgroup P) [GraphAction ↥H 𝒯] [GraphAction ↥G₂ 𝒯] (p : P)
    (Γ' : Subgroup ↥G₂) [GraphAction ↥Γ' 𝒯]
    (hΓ' : ∀ x : ↥G₂, x ∈ Γ' ↔ p * (x : P) * p⁻¹ ∈ H)
    (hHG₂ : ∀ h : P, h ∈ H → p⁻¹ * h * p ∈ G₂) (d : 𝒯.Dart) :
    Nat.card (stabilizer ↥Γ' (p⁻¹ • d)) = Nat.card (stabilizer ↥H d) := by
  refine Nat.card_congr
    { toFun := fun γ => ⟨⟨p * ((γ.1 : ↥G₂) : P) * p⁻¹, (hΓ' γ.1).1 γ.1.2⟩, ?_⟩
      invFun := fun h => ⟨⟨⟨p⁻¹ * (h.1 : P) * p, hHG₂ _ h.1.2⟩, (hΓ' _).2 ?_⟩, ?_⟩
      left_inv := fun γ => Subtype.ext (Subtype.ext (Subtype.ext (by
        show p⁻¹ * (p * ((γ.1 : ↥G₂) : P) * p⁻¹) * p = ((γ.1 : ↥G₂) : P); group)))
      right_inv := fun h => Subtype.ext (Subtype.ext (by
        show p * (p⁻¹ * (h.1 : P) * p) * p⁻¹ = (h.1 : P); group)) }
  ·
    have hγ : ((γ.1 : ↥G₂) : P) • (p⁻¹ • d) = p⁻¹ • d := mem_stabilizer_iff.mp γ.2
    show (p * ((γ.1 : ↥G₂) : P) * p⁻¹) • d = d
    rw [mul_smul, mul_smul, hγ, smul_inv_smul]
  · show p * (p⁻¹ * (h.1 : P) * p) * p⁻¹ ∈ H
    rw [show p * (p⁻¹ * (h.1 : P) * p) * p⁻¹ = (h.1 : P) by group]; exact h.1.2
  · have hh : (h.1 : P) • d = d := mem_stabilizer_iff.mp h.2
    show (p⁻¹ * (h.1 : P) * p) • (p⁻¹ • d) = p⁻¹ • d
    rw [mul_smul, mul_smul, smul_inv_smul, hh]

theorem finiteIndex_of_finite_orbitQuotient_of_finite_stabilizer {H X : Type} [Group H] [MulAction H X]
    (K : Subgroup H) (x₀ : X) [Finite (orbitRel.Quotient ↥K X)] [Finite (stabilizer H x₀)] :
    K.FiniteIndex := by
  classical

  let g : H ⧸ K → orbitRel.Quotient ↥K X :=
    Quotient.lift (fun h : H => (Quotient.mk _ (h⁻¹ • x₀) : orbitRel.Quotient ↥K X)) (by
      intro a b hab
      apply Quotient.sound
      refine ⟨⟨a⁻¹ * b, QuotientGroup.leftRel_apply.mp hab⟩, ?_⟩
      show (a⁻¹ * b) • (b⁻¹ • x₀) = a⁻¹ • x₀
      rw [mul_smul, smul_inv_smul])

  have hfib : ∀ h₁ h₂ : H, g (QuotientGroup.mk h₁) = g (QuotientGroup.mk h₂) →
      ∃ s : stabilizer H x₀, (QuotientGroup.mk h₂ : H ⧸ K) = QuotientGroup.mk ((s : H)⁻¹ * h₁) := by
    intro h₁ h₂ h12
    obtain ⟨k, hk⟩ : ∃ k : ↥K, k • (h₂⁻¹ • x₀) = h₁⁻¹ • x₀ := Quotient.exact h12
    have hk' : (k : H) • (h₂⁻¹ • x₀) = h₁⁻¹ • x₀ := hk
    refine ⟨⟨h₁ * (k : H) * h₂⁻¹, ?_⟩, ?_⟩
    · rw [mem_stabilizer_iff, mul_smul, mul_smul, hk', smul_inv_smul]
    · apply Quotient.sound
      refine QuotientGroup.leftRel_apply.mpr ?_
      rw [show h₂⁻¹ * ((h₁ * (k : H) * h₂⁻¹)⁻¹ * h₁) = ((k⁻¹ : ↥K) : H) by
        rw [Subgroup.coe_inv]; group]
      exact (k⁻¹).2

  haveI : Finite (H ⧸ K) := by
    let sec : orbitRel.Quotient ↥K X → H ⧸ K := fun q =>
      if hq : ∃ c : H ⧸ K, g c = q then hq.choose else QuotientGroup.mk 1
    refine Finite.of_surjective (fun sq : stabilizer H x₀ × orbitRel.Quotient ↥K X =>
      Quotient.map' (fun h : H => (sq.1 : H)⁻¹ * h) (fun a b hab => QuotientGroup.leftRel_apply.mpr (by
        rw [show ((sq.1 : H)⁻¹ * a)⁻¹ * ((sq.1 : H)⁻¹ * b) = a⁻¹ * b by group]
        exact QuotientGroup.leftRel_apply.mp hab)) (sec (sq.2))) ?_
    intro c
    induction c using QuotientGroup.induction_on with
    | H h =>
      have hq : ∃ c : H ⧸ K, g c = g (QuotientGroup.mk h) := ⟨_, rfl⟩
      have hsec : sec (g (QuotientGroup.mk h)) = hq.choose := dif_pos hq
      obtain ⟨h₀, hh₀⟩ := Quotient.exists_rep hq.choose
      have hg : g (QuotientGroup.mk h₀) = g (QuotientGroup.mk h) := by
        rw [show (QuotientGroup.mk h₀ : H ⧸ K) = hq.choose from hh₀]; exact hq.choose_spec
      obtain ⟨s, hs⟩ := hfib h₀ h hg
      refine ⟨(s, g (QuotientGroup.mk h)), ?_⟩
      show Quotient.map' _ _ (sec (g (QuotientGroup.mk h))) = QuotientGroup.mk h
      rw [hsec, ← hh₀, hs]
      rfl
  exact Subgroup.finiteIndex_of_finite_quotient

end Skel
end

namespace Skel

def conjEquiv {P : Type} [Group P] (H G₂ : Subgroup P) (p : P) (Γ' : Subgroup ↥G₂)
    (hΓ' : ∀ x : ↥G₂, x ∈ Γ' ↔ p * (x : P) * p⁻¹ ∈ H)
    (hHG₂ : ∀ h : P, h ∈ H → p⁻¹ * h * p ∈ G₂) : ↥Γ' ≃* ↥H where
  toFun γ := ⟨p * ((γ : ↥G₂) : P) * p⁻¹, (hΓ' (γ : ↥G₂)).1 γ.2⟩
  invFun h := ⟨⟨p⁻¹ * (h : P) * p, hHG₂ _ h.2⟩, (hΓ' _).2 (by
    rw [show p * (p⁻¹ * (h : P) * p) * p⁻¹ = (h : P) by group]; exact h.2)⟩
  left_inv γ := Subtype.ext (Subtype.ext (by
    show p⁻¹ * (p * ((γ : ↥G₂) : P) * p⁻¹) * p = ((γ : ↥G₂) : P); group))
  right_inv h := Subtype.ext (by show p * (p⁻¹ * (h : P) * p) * p⁻¹ = (h : P); group)
  map_mul' γ γ' := Subtype.ext (by
    show p * (((γ * γ' : ↥Γ') : ↥G₂) : P) * p⁻¹ = (p * ((γ : ↥G₂) : P) * p⁻¹) * (p * ((γ' : ↥G₂) : P) * p⁻¹)
    rw [Subgroup.coe_mul, Subgroup.coe_mul]; group)

theorem conjEquiv_apply_coe {P : Type} [Group P] (H G₂ : Subgroup P) (p : P) (Γ' : Subgroup ↥G₂)
    (hΓ' : ∀ x : ↥G₂, x ∈ Γ' ↔ p * (x : P) * p⁻¹ ∈ H)
    (hHG₂ : ∀ h : P, h ∈ H → p⁻¹ * h * p ∈ G₂) (γ : ↥Γ') :
    ((conjEquiv H G₂ p Γ' hΓ' hHG₂ γ : ↥H) : P) = p * ((γ : ↥G₂) : P) * p⁻¹ := rfl

noncomputable def qChar {H : Type} [Group H] {Z : Type} [AddCommGroup Z] [Module ℤ Z] {C : Type} [Field C] [Algebra ℚ C]
    (Kp : IntermediateField ℚ C)
    (Φ : Additive (Abelianization H) →+ Z) (qx : Z →ₗ[ℤ] Additive (↥Kp)ˣ) : H →* Cˣ :=
  (Units.map ((algebraMap ↥Kp C : ↥Kp →+* C) : ↥Kp →* C)).comp
    (AddMonoidHom.toMultiplicative (qx.toAddMonoidHom.comp (Φ.comp (MonoidHom.toAdditive (Abelianization.of (G := H))))))

theorem qChar_apply {H : Type} [Group H] {Z : Type} [AddCommGroup Z] [Module ℤ Z] {C : Type} [Field C] [Algebra ℚ C]
    (Kp : IntermediateField ℚ C)
    (Φ : Additive (Abelianization H) →+ Z) (qx : Z →ₗ[ℤ] Additive (↥Kp)ˣ) (β : H) :
    ((qChar Kp Φ qx β : Cˣ) : C) = (((Additive.toMul (qx (Φ (Additive.ofMul (Abelianization.of β)))) : (↥Kp)ˣ) : ↥Kp) : C) := rfl

noncomputable def qCharInv {H : Type} [Group H] {Z : Type} [AddCommGroup Z] [Module ℤ Z] {C : Type} [Field C] [Algebra ℚ C]
    (Kp : IntermediateField ℚ C)
    (Φ : Additive (Abelianization H) →+ Z) (qx : Z →ₗ[ℤ] Additive (↥Kp)ˣ) : H →* Cˣ :=
  (qChar Kp Φ qx)⁻¹

theorem qCharInv_apply {H : Type} [Group H] {Z : Type} [AddCommGroup Z] [Module ℤ Z] {C : Type} [Field C] [Algebra ℚ C]
    (Kp : IntermediateField ℚ C)
    (Φ : Additive (Abelianization H) →+ Z) (qx : Z →ₗ[ℤ] Additive (↥Kp)ˣ) (β : H) :
    ((qCharInv Kp Φ qx β : Cˣ) : C) = ((((Additive.toMul (qx (Φ (Additive.ofMul (Abelianization.of β)))) : (↥Kp)ˣ) : ↥Kp) : C))⁻¹ := by
  rw [qCharInv, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
  rfl

end Skel

theorem Skel.comp_transfer {G : Type*} [Group G] {H : Subgroup G} [H.FiniteIndex]
    {A B : Type*} [CommGroup A] [CommGroup B] (ϕ : ↥H →* A) (f : A →* B) :
    f.comp ϕ.transfer = (f.comp ϕ).transfer := by
  ext g
  rw [MonoidHom.comp_apply, MonoidHom.transfer_def ϕ default g, MonoidHom.transfer_def (f.comp ϕ) default g]
  unfold Subgroup.leftTransversals.diff
  simp only [map_prod, MonoidHom.comp_apply]

section
open MulAction
open scoped Pointwise

namespace BP

section Tree

variable {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
  (hT : 𝒯.IsTree) [DecidableEq (QuotEdge G 𝒯)] {E : Type} (orb : E → QuotEdge G 𝒯)

noncomputable def treePath (v₀ x : W) : 𝒯.Path v₀ x := somePath (hT.connected.preconnected v₀ x)

noncomputable def pot (v₀ x : W) : E → ℤ := walkCycle 𝒯 orb (treePath 𝒯 hT v₀ x : 𝒯.Walk v₀ x)

theorem pot_self (v₀ : W) : pot 𝒯 hT orb v₀ v₀ = 0 := by
  unfold pot
  rw [hT.isAcyclic.path_unique (treePath 𝒯 hT v₀ v₀) SimpleGraph.Path.nil]
  exact walkCycle_nil 𝒯 orb v₀

theorem pot_adj (v₀ : W) {u w : W} (h : 𝒯.Adj u w) :
    pot 𝒯 hT orb v₀ w = pot 𝒯 hT orb v₀ u +
      walkCycle 𝒯 orb (SimpleGraph.Walk.cons h SimpleGraph.Walk.nil : 𝒯.Walk u w) := by
  classical
  unfold pot
  set P := treePath 𝒯 hT v₀ u with hP
  by_cases hw : w ∈ (P : 𝒯.Walk v₀ u).support
  · have hspec := SimpleGraph.Walk.take_spec (P : 𝒯.Walk v₀ u) hw
    have htake : (P : 𝒯.Walk v₀ u).takeUntil w hw = (treePath 𝒯 hT v₀ w : 𝒯.Walk v₀ w) :=
      congrArg Subtype.val (hT.isAcyclic.path_unique ⟨_, P.2.takeUntil hw⟩ (treePath 𝒯 hT v₀ w))
    have hdrop : (P : 𝒯.Walk v₀ u).dropUntil w hw =
        (SimpleGraph.Walk.cons h.symm SimpleGraph.Walk.nil : 𝒯.Walk w u) :=
      congrArg Subtype.val (hT.isAcyclic.path_unique ⟨_, P.2.dropUntil hw⟩ (SimpleGraph.Path.singleton h.symm))
    rw [← hspec, walkCycle_append, htake, hdrop]
    have hrev : (SimpleGraph.Walk.cons h.symm SimpleGraph.Walk.nil : 𝒯.Walk w u) =
        (SimpleGraph.Walk.cons h SimpleGraph.Walk.nil : 𝒯.Walk u w).reverse := by
      simp
    rw [hrev, walkCycle_reverse]
    abel
  · have hpath : ((P : 𝒯.Walk v₀ u).concat h).IsPath := (SimpleGraph.Walk.concat_isPath_iff h).mpr ⟨P.2, hw⟩
    have := hT.isAcyclic.path_unique ⟨_, hpath⟩ (treePath 𝒯 hT v₀ w)
    rw [← congrArg Subtype.val this]
    show walkCycle 𝒯 orb ((P : 𝒯.Walk v₀ u).concat h) = _
    rw [SimpleGraph.Walk.concat_eq_append, walkCycle_append]

theorem walkCycle_eq_pot_sub_pot (v₀ : W) {x y : W} (p : 𝒯.Walk x y) :
    walkCycle 𝒯 orb p = pot 𝒯 hT orb v₀ y - pot 𝒯 hT orb v₀ x := by
  induction p with
  | nil => rw [walkCycle_nil, sub_self]
  | @cons u w z h p ih =>
    have : (SimpleGraph.Walk.cons h p : 𝒯.Walk u z) =
        (SimpleGraph.Walk.cons h SimpleGraph.Walk.nil : 𝒯.Walk u w).append p := rfl
    rw [this, walkCycle_append, ih, pot_adj 𝒯 hT orb v₀ h]
    abel

theorem pathCycle_eq_pot (v₀ : W) (g : G) : pathCycle 𝒯 orb v₀ g = pot 𝒯 hT orb v₀ (g • v₀) :=
  pathCycle_eq_walkCycle 𝒯 orb hT.isAcyclic v₀ g (treePath 𝒯 hT v₀ (g • v₀))

theorem walkCycle_copy {u v u' v' : W} (p : 𝒯.Walk u v) (hu : u = u') (hv : v = v') :
    walkCycle 𝒯 orb (p.copy hu hv) = walkCycle 𝒯 orb p := by
  subst hu hv; rfl

include hT in

theorem pathCycle_mul (v₀ : W) (g h : G) :
    pathCycle 𝒯 orb v₀ (g * h) = pathCycle 𝒯 orb v₀ g + pathCycle 𝒯 orb v₀ h := by
  rw [pathCycle_eq_pot 𝒯 hT, pathCycle_eq_pot 𝒯 hT, pathCycle_eq_pot 𝒯 hT]
  have h1 := walkCycle_eq_pot_sub_pot 𝒯 hT orb v₀
    ((((treePath 𝒯 hT v₀ (h • v₀) : 𝒯.Walk v₀ (h • v₀)).map (smulHom g)).copy rfl (mul_smul g h v₀).symm))
  rw [walkCycle_copy, walkCycle_map_smulHom] at h1
  change pot 𝒯 hT orb v₀ (h • v₀) = _ at h1
  simp only [smulHom_apply] at h1
  rw [h1]
  abel

include hT in
theorem pathCycle_one (v₀ : W) : pathCycle 𝒯 orb v₀ 1 = 0 := by
  rw [pathCycle_eq_pot 𝒯 hT, one_smul, pot_self]

end Tree

end BP

namespace NatOmegaBS

open CerednikDrinfeld CerednikDrinfeld.Mumford MulAction

section generic

variable {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
  (Γ' : Subgroup G) [GraphAction ↥Γ' 𝒯]

theorem subgroup_smul_dart (γ : ↥Γ') (d : 𝒯.Dart) : γ • d = (γ : G) • d := rfl

theorem mk_out_eq (d : 𝒯.Dart) :
    (Quotient.mk (orbitRel G 𝒯.Dart) ((Quotient.mk (orbitRel ↥Γ' 𝒯.Dart) d : QuotEdge ↥Γ' 𝒯).out) : QuotEdge G 𝒯) =
      Quotient.mk (orbitRel G 𝒯.Dart) d := by
  have h : (orbitRel ↥Γ' 𝒯.Dart) ((Quotient.mk (orbitRel ↥Γ' 𝒯.Dart) d : QuotEdge ↥Γ' 𝒯).out) d :=
    Quotient.mk_out d
  rw [orbitRel_apply, mem_orbit_iff] at h
  obtain ⟨γ, hγ⟩ := h
  rw [← hγ, subgroup_smul_dart, quotEdge_mk_smul]

theorem tau_out_fst_eq (τ : W → ZMod 2) (hτ : ∀ (g : G) (w : W), τ (g • w) = τ w) (d : 𝒯.Dart) :
    τ ((Quotient.mk (orbitRel G 𝒯.Dart) d : QuotEdge G 𝒯).out).fst = τ d.fst := by
  have h : (orbitRel G 𝒯.Dart) ((Quotient.mk (orbitRel G 𝒯.Dart) d : QuotEdge G 𝒯).out) d := Quotient.mk_out d
  rw [orbitRel_apply, mem_orbit_iff] at h
  obtain ⟨g, hg⟩ := h
  rw [← hg, smul_dart_fst, hτ]

end generic

theorem sum_list_map_sum {ι α β : Type} [AddCommMonoid β] (s : Finset ι) (l : List α) (f : ι → α → β) :
    ∑ i ∈ s, (l.map (f i)).sum = (l.map fun a => ∑ i ∈ s, f i a).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [Finset.sum_add_distrib, ih]

end NatOmegaBS

namespace NatOmegaPull

theorem transfer_eq_prod_of_section {G : Type} [Group G] (H : Subgroup G) [H.FiniteIndex] [Fintype (G ⧸ H)]
    {A : Type} [CommGroup A] (ϕ : ↥H →* A) (s : G ⧸ H → G) (hs : ∀ q : G ⧸ H, (QuotientGroup.mk (s q) : G ⧸ H) = q)
    (g : G) :
    ∃ u : G ⧸ H → ↥H, (∀ q, (u q : G) = (s q)⁻¹ * (g * s (g⁻¹ • q))) ∧ MonoidHom.transfer ϕ g = ∏ q, ϕ (u q) := by
  classical
  have hmem : ∀ q : G ⧸ H, (s q)⁻¹ * (g * s (g⁻¹ • q)) ∈ H := by
    intro q
    rw [← QuotientGroup.eq, hs, ← smul_eq_mul, ← MulAction.Quotient.smul_coe, hs, smul_inv_smul]
  refine ⟨fun q => ⟨_, hmem q⟩, fun q => rfl, ?_⟩
  let T : H.LeftTransversal := ⟨Set.range s, Subgroup.isComplement_range_left hs⟩
  rw [MonoidHom.transfer_def ϕ T g]
  unfold Subgroup.leftTransversals.diff
  dsimp only
  refine Finset.prod_congr (Finset.ext fun q => by simp) fun q _ => congrArg ϕ (Subtype.ext ?_)
  show ((T.2.leftQuotientEquiv q : G))⁻¹ * ((g • T).2.leftQuotientEquiv q : G) = (s q)⁻¹ * (g * s (g⁻¹ • q))
  rw [Subgroup.smul_apply_eq_smul_apply_inv_smul, smul_eq_mul]
  erw [Subgroup.IsComplement.leftQuotientEquiv_apply hs, Subgroup.IsComplement.leftQuotientEquiv_apply hs]

theorem map_ofMul_prod {M A : Type} [CommMonoid M] [AddCommMonoid A] (Φ : Additive M →+ A) {ι : Type}
    (s : Finset ι) (f : ι → M) :
    Φ (Additive.ofMul (∏ i ∈ s, f i)) = ∑ i ∈ s, Φ (Additive.ofMul (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ofMul_mul, map_add, ih]

section Count

variable {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
  (Γ' : Subgroup G) [GraphAction ↥Γ' 𝒯]

theorem sum_ite_mk_smul_eq [Fintype (G ⧸ Γ')] [DecidableEq (QuotEdge G 𝒯)] [DecidableEq (QuotEdge ↥Γ' 𝒯)] (s : G ⧸ Γ' → G) (hs : ∀ q : G ⧸ Γ', (QuotientGroup.mk (s q) : G ⧸ Γ') = q)
    (d₁ : 𝒯.Dart) (hfree : stabilizer G d₁ = ⊥) (x : 𝒯.Dart) :
    (∑ q : G ⧸ Γ', if (Quotient.mk (orbitRel ↥Γ' 𝒯.Dart) ((s q)⁻¹ • x) : QuotEdge ↥Γ' 𝒯) =
        Quotient.mk (orbitRel ↥Γ' 𝒯.Dart) d₁ then (1 : ℤ) else 0) =
      if (Quotient.mk (orbitRel G 𝒯.Dart) x : QuotEdge G 𝒯) = Quotient.mk (orbitRel G 𝒯.Dart) d₁ then 1 else 0 := by
  classical

  have hiff : ∀ q : G ⧸ Γ', (Quotient.mk (orbitRel ↥Γ' 𝒯.Dart) ((s q)⁻¹ • x) : QuotEdge ↥Γ' 𝒯) =
      Quotient.mk (orbitRel ↥Γ' 𝒯.Dart) d₁ ↔ ∃ h : ↥Γ', x = (s q * (h : G)) • d₁ := by
    intro q
    rw [Quotient.eq]
    change (s q)⁻¹ • x ∈ orbit ↥Γ' d₁ ↔ _
    rw [mem_orbit_iff]
    constructor
    · rintro ⟨h, hh⟩
      refine ⟨h, ?_⟩
      rw [mul_smul, ← NatOmegaBS.subgroup_smul_dart 𝒯 Γ' h d₁, hh, smul_inv_smul]
    · rintro ⟨h, hh⟩
      refine ⟨h, ?_⟩
      rw [hh, mul_smul, inv_smul_smul, NatOmegaBS.subgroup_smul_dart 𝒯 Γ' h d₁]
  by_cases hx : (Quotient.mk (orbitRel G 𝒯.Dart) x : QuotEdge G 𝒯) = Quotient.mk (orbitRel G 𝒯.Dart) d₁
  · rw [if_pos hx]
    have hx' : x ∈ orbit G d₁ := by rwa [Quotient.eq] at hx
    obtain ⟨g, rfl⟩ := mem_orbit_iff.mp hx'

    have hq₀ : ∃ h : ↥Γ', g • d₁ = (s (QuotientGroup.mk g) * (h : G)) • d₁ := by
      have hmem : (s (QuotientGroup.mk g))⁻¹ * g ∈ Γ' := by rw [← QuotientGroup.eq, hs]
      exact ⟨⟨_, hmem⟩, by rw [mul_inv_cancel_left]⟩
    rw [Finset.sum_eq_single_of_mem (QuotientGroup.mk g) (Finset.mem_univ _)]
    · rw [if_pos ((hiff _).mpr hq₀)]
    · intro q _ hq
      rw [if_neg]
      intro h
      obtain ⟨h', hh'⟩ := (hiff q).mp h

      have hstab : g⁻¹ * (s q * (h' : G)) ∈ stabilizer G d₁ := by
        rw [mem_stabilizer_iff, mul_smul, ← hh', inv_smul_smul]
      rw [hfree, Subgroup.mem_bot] at hstab
      have hg : s q * (h' : G) = g := (inv_mul_eq_one.mp hstab).symm
      apply hq
      rw [← hs q, ← hg, QuotientGroup.mk_mul_of_mem _ h'.2]
  · rw [if_neg hx]
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [if_neg]
    intro h
    obtain ⟨h', hh'⟩ := (hiff q).mp h
    apply hx
    rw [hh', quotEdge_mk_smul]

theorem walkCycle_map_smulHom_apply [DecidableEq (QuotEdge ↥Γ' 𝒯)] {E : Type} (orb : E → QuotEdge ↥Γ' 𝒯)
    (g : G) {u v : W} (p : 𝒯.Walk u v) (e : E) :
    walkCycle 𝒯 orb (p.map (smulHom (𝒯 := 𝒯) g)) e = (p.darts.map fun d => dartIndex 𝒯 (orb e) (g • d)).sum := by
  induction p with
  | nil => simp [walkCycle]
  | cons h p ih =>
    rw [SimpleGraph.Walk.map_cons, walkCycle_cons, ih, SimpleGraph.Walk.darts_cons, List.map_cons, List.sum_cons]
    rfl

end Count

end NatOmegaPull

namespace NatOmegaPullW

variable {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
  (Γ' : Subgroup G) [GraphAction ↥Γ' 𝒯]

omit [GraphAction ↥Γ' 𝒯] in
private theorem _root_.NatOmegaPullW.subgroup_smul_dart (γ : ↥Γ') (d : 𝒯.Dart) : γ • d = (γ : G) • d := rfl

p2m_export "NatOmegaPullW" "subgroup_smul_dart"

theorem stabilizer_subgroup_mk_one (S : Subgroup G) :
    stabilizer ↥S ((QuotientGroup.mk (1 : G)) : G ⧸ Γ') = Γ'.subgroupOf S := by
  ext σ
  rw [mem_stabilizer_iff, Subgroup.mem_subgroupOf]
  change ((σ : G) • (QuotientGroup.mk (1 : G) : G ⧸ Γ') = QuotientGroup.mk 1) ↔ (σ : G) ∈ Γ'
  rw [MulAction.Quotient.smul_coe, smul_eq_mul, mul_one, QuotientGroup.eq, mul_one, inv_mem_iff]

theorem sum_ite_mk_smul_eq_relIndex [Γ'.FiniteIndex] [Fintype (G ⧸ Γ')] [DecidableEq (QuotEdge G 𝒯)]
    [DecidableEq (QuotEdge ↥Γ' 𝒯)]
    (s : G ⧸ Γ' → G) (hs : ∀ q : G ⧸ Γ', (QuotientGroup.mk (s q) : G ⧸ Γ') = q) (d₁ x : 𝒯.Dart) :
    (∑ q : G ⧸ Γ', if (Quotient.mk (orbitRel ↥Γ' 𝒯.Dart) ((s q)⁻¹ • x) : QuotEdge ↥Γ' 𝒯) =
        Quotient.mk (orbitRel ↥Γ' 𝒯.Dart) d₁ then (1 : ℤ) else 0) =
      if (Quotient.mk (orbitRel G 𝒯.Dart) x : QuotEdge G 𝒯) = Quotient.mk (orbitRel G 𝒯.Dart) d₁ then
        (Γ'.relIndex (stabilizer G d₁) : ℤ) else 0 := by
  classical
  set S : Subgroup G := stabilizer G d₁ with hSdef
  have hiff : ∀ q : G ⧸ Γ', (Quotient.mk (orbitRel ↥Γ' 𝒯.Dart) ((s q)⁻¹ • x) : QuotEdge ↥Γ' 𝒯) =
      Quotient.mk (orbitRel ↥Γ' 𝒯.Dart) d₁ ↔ ∃ h : ↥Γ', x = (s q * (h : G)) • d₁ := by
    intro q
    rw [Quotient.eq]
    change (s q)⁻¹ • x ∈ orbit ↥Γ' d₁ ↔ _
    rw [mem_orbit_iff]
    constructor
    · rintro ⟨h, hh⟩
      exact ⟨h, by rw [mul_smul, ← subgroup_smul_dart 𝒯 Γ' h d₁, hh, smul_inv_smul]⟩
    · rintro ⟨h, hh⟩
      exact ⟨h, by rw [hh, mul_smul, inv_smul_smul, subgroup_smul_dart 𝒯 Γ' h d₁]⟩
  by_cases hx : (Quotient.mk (orbitRel G 𝒯.Dart) x : QuotEdge G 𝒯) = Quotient.mk (orbitRel G 𝒯.Dart) d₁
  · rw [if_pos hx]
    have hx' : x ∈ orbit G d₁ := by rwa [Quotient.eq] at hx
    obtain ⟨g₀, rfl⟩ := mem_orbit_iff.mp hx'

    have hP : ∀ q : G ⧸ Γ', (∃ h : ↥Γ', g₀ • d₁ = (s q * (h : G)) • d₁) ↔
        q ∈ g₀ • orbit ↥S ((QuotientGroup.mk (1 : G)) : G ⧸ Γ') := by
      intro q
      rw [Set.mem_smul_set]
      constructor
      · rintro ⟨h, hh⟩
        have hσ : g₀⁻¹ * (s q * (h : G)) ∈ S := by
          rw [hSdef, mem_stabilizer_iff, mul_smul, ← hh, inv_smul_smul]
        refine ⟨QuotientGroup.mk (g₀⁻¹ * (s q * (h : G))), ⟨⟨_, hσ⟩, ?_⟩, ?_⟩
        · change ((⟨_, hσ⟩ : ↥S) : G) • (QuotientGroup.mk (1 : G) : G ⧸ Γ') = _
          rw [MulAction.Quotient.smul_coe, smul_eq_mul, mul_one]
        · rw [MulAction.Quotient.smul_coe, smul_eq_mul, mul_inv_cancel_left, QuotientGroup.mk_mul_of_mem _ h.2, hs]
      · rintro ⟨q', ⟨σ, rfl⟩, rfl⟩
        have hmem : (s (g₀ • (σ • (QuotientGroup.mk (1 : G) : G ⧸ Γ'))))⁻¹ * (g₀ * (σ : G)) ∈ Γ' := by
          rw [← QuotientGroup.eq, hs]
          change g₀ • ((σ : G) • (QuotientGroup.mk (1 : G) : G ⧸ Γ')) = _
          rw [MulAction.Quotient.smul_coe, MulAction.Quotient.smul_coe, smul_eq_mul, smul_eq_mul, mul_one]
        refine ⟨⟨_, hmem⟩, ?_⟩
        rw [mul_inv_cancel_left, mul_smul, show ((σ : ↥S) : G) • d₁ = d₁ from mem_stabilizer_iff.mp (hSdef ▸ σ.2)]
    simp_rw [hiff, hP]
    rw [Finset.sum_boole]

    have hcard : (Finset.univ.filter fun q : G ⧸ Γ' =>
        q ∈ g₀ • orbit (↥S) (QuotientGroup.mk (1 : G) : G ⧸ Γ')).card = Γ'.relIndex S := by
      rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
      change Nat.card ↥(g₀ • orbit (↥S) (QuotientGroup.mk (1 : G) : G ⧸ Γ')) = _
      rw [Nat.card_coe_set_eq, Set.ncard_smul_set, ← MulAction.index_stabilizer, stabilizer_subgroup_mk_one]
      rfl
    rw [hcard]
  · rw [if_neg hx]
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [if_neg]
    intro h
    obtain ⟨h', hh'⟩ := (hiff q).mp h
    exact hx (by rw [hh', quotEdge_mk_smul])

end NatOmegaPullW

namespace NatOmegaPullW

variable {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
  (Γ' : Subgroup G) [GraphAction ↥Γ' 𝒯]

def stabilizerSubgroupEquiv (d : 𝒯.Dart) :
    ↥(stabilizer ↥Γ' d) ≃ ↥(Γ'.subgroupOf (stabilizer G d)) where
  toFun h := ⟨⟨(h.1 : G), by
      have := h.2; rw [mem_stabilizer_iff] at this ⊢; exact this⟩,
    by rw [Subgroup.mem_subgroupOf]; exact h.1.2⟩
  invFun σ := ⟨⟨(σ.1 : G), by have := σ.2; rwa [Subgroup.mem_subgroupOf] at this⟩, by
      have := σ.1.2; rw [mem_stabilizer_iff] at this ⊢; exact this⟩
  left_inv h := rfl
  right_inv σ := rfl

omit [GraphAction ↥Γ' 𝒯] in

theorem card_stabilizer_smul (g : G) (d : 𝒯.Dart) :
    Nat.card (stabilizer G (g • d)) = Nat.card (stabilizer G d) := by
  rw [stabilizer_smul_eq_stabilizer_map_conj]
  exact (Nat.card_congr ((stabilizer G d).equivMapOfInjective _ (MulAut.conj g).injective).toEquiv).symm

theorem deg_eq_relIndex [Γ'.FiniteIndex] (hfin : ∀ w : W, Finite (stabilizer G w))
    (τ : W → ZMod 2)
    {E₁ V₁ : Type} [Fintype E₁] [Fintype V₁] [DecidableEq V₁] (D₁ : DegeneracyData E₁ V₁)
    (eE₁ : E₁ ≃ {e : QuotEdge ↥Γ' 𝒯 // τ e.out.fst = 0})
    (hw₁ : ∀ e₁ : E₁, (D₁.w e₁ : ℕ) = Nat.card (stabilizer ↥Γ' (((eE₁ e₁).1).out : 𝒯.Dart)))
    {E₂ V₂ : Type} [Fintype E₂] [DecidableEq E₂] [DecidableEq V₂] (D₂ : DegeneracyData E₂ V₂)
    (eE₂ : E₂ ≃ {e : QuotEdge G 𝒯 // τ e.out.fst = 0})
    (hw₂ : ∀ e₂ : E₂, (D₂.w e₂ : ℕ) = Nat.card (stabilizer G (((eE₂ e₂).1).out : 𝒯.Dart)))
    (μ : D₁.FiniteHom D₂)
    (hμE : ∀ e₁ : E₁, ((eE₂ (μ.mapE e₁)).1 : QuotEdge G 𝒯) = Quotient.mk (orbitRel G 𝒯.Dart) ((eE₁ e₁).1).out)
    (e₁ : E₁) :
    (μ.deg e₁ : ℕ) = Γ'.relIndex (stabilizer G ((eE₁ e₁).1).out) := by
  set d₁ : 𝒯.Dart := ((eE₁ e₁).1).out with hd₁
  set S : Subgroup G := stabilizer G d₁ with hSdef

  haveI : Finite ↥S := by
    have hle : S ≤ stabilizer G d₁.fst := stabilizer_dart_le 𝒯 d₁
    haveI := hfin d₁.fst
    exact Finite.of_injective _ (Subgroup.inclusion_injective hle)

  have hrep : ((eE₂ (μ.mapE e₁)).1).out ∈ orbit G d₁ := by
    have h := Quotient.mk_out (s := orbitRel G 𝒯.Dart) ((eE₂ (μ.mapE e₁)).1).out
    have h2 : (Quotient.mk (orbitRel G 𝒯.Dart) ((eE₂ (μ.mapE e₁)).1).out : QuotEdge G 𝒯) =
        Quotient.mk (orbitRel G 𝒯.Dart) d₁ := by rw [Quotient.out_eq, hμE]
    exact Quotient.eq.mp h2
  obtain ⟨g, hg⟩ := mem_orbit_iff.mp hrep
  have hw : (μ.deg e₁ : ℕ) * Nat.card ↥(stabilizer ↥Γ' d₁) = Nat.card ↥S := by
    have := congrArg (fun x : ℕ+ => (x : ℕ)) (μ.w_mapE e₁)
    simp only [PNat.mul_coe] at this
    rw [hw₂, hw₁, ← hg, card_stabilizer_smul] at this
    exact this.symm
  have hsub : Nat.card ↥(stabilizer ↥Γ' d₁) = Nat.card ↥(Γ'.subgroupOf S) :=
    Nat.card_congr (stabilizerSubgroupEquiv 𝒯 Γ' d₁)
  have hci : Nat.card ↥(Γ'.subgroupOf S) * (Γ'.subgroupOf S).index = Nat.card ↥S := Subgroup.card_mul_index _
  have hpos : Nat.card ↥(Γ'.subgroupOf S) ≠ 0 := Nat.card_pos.ne'
  rw [hsub, ← hci, mul_comm] at hw
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hpos) hw

end NatOmegaPullW

end

namespace DegIdx

open MulAction NatOmegaBS NatOmegaPull NatOmegaPullW

variable {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
  (Γ' : Subgroup G) [GraphAction ↥Γ' 𝒯]

theorem degTotal_eq_index [Γ'.FiniteIndex] (hfin : ∀ w : W, Finite (stabilizer G w))
    (τ : W → ZMod 2) (hτ : ∀ (g : G) (w : W), τ (g • w) = τ w)
    {E₁ V₁ : Type} [Fintype E₁] [Fintype V₁] [DecidableEq V₁] (D₁ : DegeneracyData E₁ V₁)
    (eE₁ : E₁ ≃ {e : QuotEdge ↥Γ' 𝒯 // τ e.out.fst = 0})
    (hw₁ : ∀ e₁ : E₁, (D₁.w e₁ : ℕ) = Nat.card (stabilizer ↥Γ' (((eE₁ e₁).1).out : 𝒯.Dart)))
    {E₂ V₂ : Type} [Fintype E₂] [Fintype V₂] [DecidableEq E₂] [DecidableEq V₂] (D₂ : DegeneracyData E₂ V₂)
    (eE₂ : E₂ ≃ {e : QuotEdge G 𝒯 // τ e.out.fst = 0})
    (hw₂ : ∀ e₂ : E₂, (D₂.w e₂ : ℕ) = Nat.card (stabilizer G (((eE₂ e₂).1).out : 𝒯.Dart)))
    (μ : D₁.FiniteHom D₂)
    (hμE : ∀ e₁ : E₁, ((eE₂ (μ.mapE e₁)).1 : QuotEdge G 𝒯) = Quotient.mk (orbitRel G 𝒯.Dart) ((eE₁ e₁).1).out)
    (d₀ : 𝒯.Dart) (hd₀ : τ d₀.fst = 0) :
    (μ.degTotal : ℕ) = Γ'.index := by
  classical
  haveI : Fintype (G ⧸ Γ') := Fintype.ofFinite _

  have hd₀' : τ ((Quotient.mk (orbitRel G 𝒯.Dart) d₀ : QuotEdge G 𝒯).out).fst = 0 := by
    rw [tau_out_fst_eq 𝒯 τ hτ d₀]; exact hd₀
  set e₂ : E₂ := eE₂.symm ⟨Quotient.mk (orbitRel G 𝒯.Dart) d₀, hd₀'⟩ with he₂
  have he₂' : ((eE₂ e₂).1 : QuotEdge G 𝒯) = Quotient.mk (orbitRel G 𝒯.Dart) d₀ := by
    rw [he₂, Equiv.apply_symm_apply]

  have hA : (μ.degTotal : ℕ) = ∑ e₁ ∈ Finset.univ.filter (fun e₁ => μ.mapE e₁ = e₂), (μ.deg e₁ : ℕ) := by
    rw [← μ.sum_degV (D₂.a e₂)]
    have hmaps : ∀ e₁ ∈ Finset.univ.filter (fun e₁ => μ.mapE e₁ = e₂),
        D₁.a e₁ ∈ Finset.univ.filter (fun v => μ.mapV v = D₂.a e₂) := by
      intro e₁ he₁
      rw [Finset.mem_filter] at he₁ ⊢
      exact ⟨Finset.mem_univ _, by rw [← μ.a_mapE, he₁.2]⟩
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [Finset.mem_filter] at hv
    rw [← μ.sum_deg_a v e₂ hv.2.symm]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext e₁
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_comm

  have hB : ∀ e₁ : E₁, (μ.deg e₁ : ℕ) = Γ'.relIndex (stabilizer G ((eE₁ e₁).1).out) :=
    fun e₁ => deg_eq_relIndex 𝒯 Γ' hfin τ D₁ eE₁ hw₁ D₂ eE₂ hw₂ μ hμE e₁

  have hs : ∀ q : G ⧸ Γ', (QuotientGroup.mk (Quotient.out q) : G ⧸ Γ') = q := fun q => Quotient.out_eq q
  have hfib : ∀ e₁ : E₁, (Quotient.mk (orbitRel G 𝒯.Dart) d₀ : QuotEdge G 𝒯) =
      Quotient.mk (orbitRel G 𝒯.Dart) ((eE₁ e₁).1).out ↔ μ.mapE e₁ = e₂ := by
    intro e₁
    constructor
    · intro h
      apply eE₂.injective
      apply Subtype.ext
      rw [hμE, he₂']
      exact h.symm
    · intro h
      have h1 := hμE e₁
      rw [h, he₂'] at h1
      exact h1
  have hC : (Γ'.index : ℤ) = ∑ e₁ ∈ Finset.univ.filter (fun e₁ => μ.mapE e₁ = e₂),
      (Γ'.relIndex (stabilizer G ((eE₁ e₁).1).out) : ℤ) := by
    have h1 : ∀ q : G ⧸ Γ', (∑ e₁ : E₁,
        (if (Quotient.mk (orbitRel ↥Γ' 𝒯.Dart) ((Quotient.out q)⁻¹ • d₀) : QuotEdge ↥Γ' 𝒯) =
            Quotient.mk (orbitRel ↥Γ' 𝒯.Dart) ((eE₁ e₁).1).out then (1 : ℤ) else 0)) = 1 := by
      intro q
      have hτ' : ∀ (γ : ↥Γ') (w : W), τ (γ • w) = τ w := fun γ w => hτ (γ : G) w
      have hq0 : τ ((Quotient.mk (orbitRel ↥Γ' 𝒯.Dart) ((Quotient.out q)⁻¹ • d₀) : QuotEdge ↥Γ' 𝒯).out).fst = 0 := by
        rw [tau_out_fst_eq 𝒯 τ hτ' _, smul_dart_fst, hτ]; exact hd₀
      rw [Finset.sum_eq_single_of_mem (eE₁.symm ⟨_, hq0⟩) (Finset.mem_univ _)]
      · rw [if_pos]; rw [Equiv.apply_symm_apply, Quotient.out_eq]
      · intro b _ hb
        rw [if_neg]
        intro h
        apply hb
        apply eE₁.injective
        rw [Equiv.apply_symm_apply]
        apply Subtype.ext
        show ((eE₁ b).1 : QuotEdge ↥Γ' 𝒯) = _
        rw [← Quotient.out_eq ((eE₁ b).1)]
        exact h.symm
    calc (Γ'.index : ℤ) = ((Finset.univ : Finset (G ⧸ Γ')).card : ℤ) := by
          rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card, Finset.card_univ]
      _ = ∑ q : G ⧸ Γ', (1 : ℤ) := by rw [Finset.sum_const, Finset.card_univ]; simp
      _ = ∑ q : G ⧸ Γ', ∑ e₁ : E₁,
            (if (Quotient.mk (orbitRel ↥Γ' 𝒯.Dart) ((Quotient.out q)⁻¹ • d₀) : QuotEdge ↥Γ' 𝒯) =
              Quotient.mk (orbitRel ↥Γ' 𝒯.Dart) ((eE₁ e₁).1).out then (1 : ℤ) else 0) :=
          Finset.sum_congr rfl fun q _ => (h1 q).symm
      _ = ∑ e₁ : E₁, ∑ q : G ⧸ Γ',
            (if (Quotient.mk (orbitRel ↥Γ' 𝒯.Dart) ((Quotient.out q)⁻¹ • d₀) : QuotEdge ↥Γ' 𝒯) =
              Quotient.mk (orbitRel ↥Γ' 𝒯.Dart) ((eE₁ e₁).1).out then (1 : ℤ) else 0) := Finset.sum_comm
      _ = ∑ e₁ : E₁, (if (Quotient.mk (orbitRel G 𝒯.Dart) d₀ : QuotEdge G 𝒯) =
              Quotient.mk (orbitRel G 𝒯.Dart) ((eE₁ e₁).1).out then
              (Γ'.relIndex (stabilizer G ((eE₁ e₁).1).out) : ℤ) else 0) :=
          Finset.sum_congr rfl fun e₁ _ => sum_ite_mk_smul_eq_relIndex 𝒯 Γ' Quotient.out hs _ d₀
      _ = ∑ e₁ ∈ Finset.univ.filter (fun e₁ => μ.mapE e₁ = e₂),
            (Γ'.relIndex (stabilizer G ((eE₁ e₁).1).out) : ℤ) := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun e₁ _ => ?_
          simp only [hfib]

  have hZ : ((μ.degTotal : ℕ) : ℤ) = (Γ'.index : ℤ) := by
    rw [hC, hA]; push_cast
    exact Finset.sum_congr rfl fun e₁ _ => by rw [hB]
  exact_mod_cast hZ

end DegIdx

set_option maxHeartbeats 4000000 in
theorem solution
    (K₀ : Type) [Field K₀]
    (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀]
    [Finite (IsLocalRing.ResidueField R₀)]
    (G : Type) [Group G] (ρ : G →* PGL(2, K₀))
    [Mumford.GraphAction PGL(2, K₀) (BruhatTits.tree R₀ K₀)]
    (Γd : Subgroup G) (htpd : Γd.map ρ ≤ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))
    [Mumford.GraphAction ↥(Γd.map ρ) (BruhatTits.tree R₀ K₀)]
    (Ed Vd : Type) [Fintype Ed] [Fintype Vd] [DecidableEq Ed] [DecidableEq Vd]
    (Dd : DegeneracyData Ed Vd)
    (eVd : Mumford.QuotVert ↥(Γd.map ρ) (LT.LatticeTree.Vertex R₀ K₀) ≃ Vd)
    (eEd : {e : Mumford.QuotEdge ↥(Γd.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0} ≃ Ed)
    (hDad : ∀ e : {e : Mumford.QuotEdge ↥(Γd.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, Dd.a (eEd e) = eVd (Quotient.mk (MulAction.orbitRel ↥(Γd.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) e.1.out.fst))
    (hDbd : ∀ e : {e : Mumford.QuotEdge ↥(Γd.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, Dd.b (eEd e) = eVd (Quotient.mk (MulAction.orbitRel ↥(Γd.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) e.1.out.snd))
    (Γc : Subgroup G) (htpc : Γc.map ρ ≤ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))
    [Mumford.GraphAction ↥(Γc.map ρ) (BruhatTits.tree R₀ K₀)]
    (Ec Vc : Type) [Fintype Ec] [Fintype Vc] [DecidableEq Ec] [DecidableEq Vc]
    (Dc : DegeneracyData Ec Vc)
    (eVc : Mumford.QuotVert ↥(Γc.map ρ) (LT.LatticeTree.Vertex R₀ K₀) ≃ Vc)
    (eEc : {e : Mumford.QuotEdge ↥(Γc.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0} ≃ Ec)
    (hDac : ∀ e : {e : Mumford.QuotEdge ↥(Γc.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, Dc.a (eEc e) = eVc (Quotient.mk (MulAction.orbitRel ↥(Γc.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) e.1.out.fst))
    (hDbc : ∀ e : {e : Mumford.QuotEdge ↥(Γc.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, Dc.b (eEc e) = eVc (Quotient.mk (MulAction.orbitRel ↥(Γc.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) e.1.out.snd))
    (g : G) (hg : ρ g ∈ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀)) (hArr : Γd ≤ Γc.map (MulAut.conj g).toMonoidHom)
    (hDwd : ∀ e : {e : Mumford.QuotEdge ↥(Γd.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, (Dd.w (eEd e) : ℕ) = Nat.card (MulAction.stabilizer (↥(Γd.map ρ)) e.1.out))
    (hDwc : ∀ e : {e : Mumford.QuotEdge ↥(Γc.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, (Dc.w (eEc e) : ℕ) = Nat.card (MulAction.stabilizer (↥(Γc.map ρ)) e.1.out))
    (hfind : ∀ d : (BruhatTits.tree R₀ K₀).Dart, Finite (MulAction.stabilizer (↥(Γd.map ρ)) d))
    (hfinc : ∀ d : (BruhatTits.tree R₀ K₀).Dart, Finite (MulAction.stabilizer (↥(Γc.map ρ)) d))
    (μ : Dd.FiniteHom Dc)
    (hμV : ∀ v : LT.LatticeTree.Vertex R₀ K₀, μ.mapV (eVd (Quotient.mk (MulAction.orbitRel ↥(Γd.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) v)) =
      eVc (Quotient.mk (MulAction.orbitRel ↥(Γc.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) ((ρ g)⁻¹ • v)))
    (hμE : ∀ e : {e : Mumford.QuotEdge ↥(Γd.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, ((eEc.symm (μ.mapE (eEd e))).1) =
      Quotient.mk (MulAction.orbitRel ↥(Γc.map ρ) (BruhatTits.tree R₀ K₀).Dart) ((ρ g)⁻¹ • e.1.out)) :
    (μ.degTotal : ℕ) = ((Γd.map ρ).comap ((MulAut.conj (ρ g)).toMonoidHom.comp (Γc.map ρ).subtype)).index := by
  classical

  have hT : (BruhatTits.tree R₀ K₀).IsTree := CerednikDrinfeld.BruhatTits.tree_isTree R₀ K₀
  have hcb := CerednikDrinfeld.BruhatTits.tree_connected_and_colorable_two R₀ K₀
  have hadj : ∀ u v : LT.LatticeTree.Vertex R₀ K₀, (BruhatTits.tree R₀ K₀).Adj u v →
      Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) u ≠ Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) v := by
    have hadj' := (CerednikDrinfeld.Mumford.vertexType_add_one_of_adj_and_vertexType_smul_and_exists_typeCharacter
      PGL(2, K₀) (BruhatTits.tree R₀ K₀) hcb.1 hcb.2 (LT.LatticeTree.stdVertex R₀ K₀)).1
    intro u v huv h
    have h1 := hadj' u v huv
    rw [← h] at h1
    exact one_ne_zero (add_left_cancel (h1.symm.trans (add_zero _).symm))
  have hτd : ∀ (g : ↥(Γd.map ρ)) (w : LT.LatticeTree.Vertex R₀ K₀),
      Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) (g • w) = Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) w :=
    fun g w => (Mumford.mem_typePreserving_iff (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) (g : PGL(2, K₀))).1 (htpd g.2) w
  have hτc : ∀ (g : ↥(Γc.map ρ)) (w : LT.LatticeTree.Vertex R₀ K₀),
      Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) (g • w) = Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) w :=
    fun g w => (Mumford.mem_typePreserving_iff (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) (g : PGL(2, K₀))).1 (htpc g.2) w

  have haBSd : ∀ e : Ed, eVd.symm (Dd.a e) = Quotient.mk (MulAction.orbitRel ↥(Γd.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) (eEd.symm e).1.out.fst :=
    fun e => eVd.symm_apply_eq.mpr (by have h := hDad (eEd.symm e); rwa [Equiv.apply_symm_apply] at h)
  have hbBSd : ∀ e : Ed, eVd.symm (Dd.b e) = Quotient.mk (MulAction.orbitRel ↥(Γd.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) (eEd.symm e).1.out.snd :=
    fun e => eVd.symm_apply_eq.mpr (by have h := hDbd (eEd.symm e); rwa [Equiv.apply_symm_apply] at h)
  have haBSc : ∀ e : Ec, eVc.symm (Dc.a e) = Quotient.mk (MulAction.orbitRel ↥(Γc.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) (eEc.symm e).1.out.fst :=
    fun e => eVc.symm_apply_eq.mpr (by have h := hDac (eEc.symm e); rwa [Equiv.apply_symm_apply] at h)
  have hbBSc : ∀ e : Ec, eVc.symm (Dc.b e) = Quotient.mk (MulAction.orbitRel ↥(Γc.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) (eEc.symm e).1.out.snd :=
    fun e => eVc.symm_apply_eq.mpr (by have h := hDbc (eEc.symm e); rwa [Equiv.apply_symm_apply] at h)

  obtain ⟨Φd, hΦBSd⟩ := CerednikDrinfeld.Mumford.exists_addMonoidHom_abelianization_ribbonKernel_apply_eq_pathCycle
    (BruhatTits.tree R₀ K₀) hT (Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀)) hτd hadj
    Dd eEd.symm eVd.symm haBSd hbBSd (LT.LatticeTree.stdVertex R₀ K₀)

  have hHG₂ : ∀ h : PGL(2, K₀), h ∈ Γd.map ρ → (ρ g)⁻¹ * h * ρ g ∈ Γc.map ρ := by
    rintro h ⟨γ, hγ, rfl⟩
    obtain ⟨γ', hγ', hconj⟩ := Subgroup.mem_map.mp (hArr hγ)
    refine ⟨g⁻¹ * γ * g, ?_, by simp [map_mul, map_inv]⟩
    have : g⁻¹ * γ * g = γ' := by
      rw [← hconj]; simp [MulAut.conj_apply, mul_assoc]
    rw [this]; exact hγ'
  let Γ' : Subgroup ↥(Γc.map ρ) :=
    (Γd.map ρ).comap ((MulAut.conj (ρ g)).toMonoidHom.comp (Γc.map ρ).subtype)
  have hΓ' : ∀ x : ↥(Γc.map ρ), x ∈ Γ' ↔ ρ g * (x : PGL(2, K₀)) * (ρ g)⁻¹ ∈ Γd.map ρ := by
    intro x
    simp only [Γ', Subgroup.mem_comap, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  haveI : Mumford.GraphAction ↥Γ' (BruhatTits.tree R₀ K₀) := Skel.graphAction_subgroup (BruhatTits.tree R₀ K₀) Γ'
  have hp : ∀ w : LT.LatticeTree.Vertex R₀ K₀,
      Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) (ρ g • w) =
        Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) w :=
    (Mumford.mem_typePreserving_iff _ _ _).1 hg

  have hCT :=
    CerednikDrinfeld.Mumford.exists_presentation_conj_apply_eq_of_apply_eq_pathCycle
      (BruhatTits.tree R₀ K₀) hT (Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀)) hadj
      (Γd.map ρ) hτd (ρ g) hp (Γc.map ρ) hHG₂ Γ' hΓ'
      Dd eEd.symm eVd.symm haBSd hbBSd (LT.LatticeTree.stdVertex R₀ K₀) Φd hΦBSd
  obtain ⟨eE', eV', Φ', heE', heV', ha', hb', hΦ', hΦ'conj⟩ := hCT

  have hμE' : ∀ e₁ : Ed,
      ((eEc.symm (μ.mapE e₁)).1 : Mumford.QuotEdge ↥(Γc.map ρ) (BruhatTits.tree R₀ K₀)) =
        Quotient.mk (MulAction.orbitRel ↥(Γc.map ρ) (BruhatTits.tree R₀ K₀).Dart) ((eE' e₁).1).out := by
    intro e₁
    have h1 := hμE (eEd.symm e₁)
    rw [Equiv.apply_symm_apply] at h1
    rw [h1]
    have h2 := heE' e₁
    obtain ⟨γ', hγ'⟩ : ∃ γ' : ↥Γ', γ' • ((ρ g)⁻¹ • (eEd.symm e₁).1.out) = ((eE' e₁).1).out :=
      Quotient.exact ((Quotient.out_eq ((eE' e₁).1)).trans h2)
    refine Quotient.sound ⟨((γ'⁻¹ : ↥Γ') : ↥(Γc.map ρ)), ?_⟩
    rw [← hγ']
    show ((γ'⁻¹ : ↥Γ') : ↥(Γc.map ρ)) • ((γ' : ↥(Γc.map ρ)) • ((ρ g)⁻¹ • (eEd.symm e₁).1.out)) = _
    rw [Subgroup.coe_inv, inv_smul_smul]

  have hw₂ : ∀ e₂ : Ec, (Dc.w e₂ : ℕ) =
      Nat.card (MulAction.stabilizer ↥(Γc.map ρ) (((eEc.symm e₂).1).out : (BruhatTits.tree R₀ K₀).Dart)) := by
    intro e₂
    have h := hDwc (eEc.symm e₂)
    rwa [Equiv.apply_symm_apply] at h
  have hfinV : ∀ w : LT.LatticeTree.Vertex R₀ K₀, Finite (MulAction.stabilizer ↥(Γc.map ρ) w) :=
    CerednikDrinfeld.BruhatTits.finite_stabilizer_vertex_of_finite_stabilizer_dart R₀ K₀ ↥(Γc.map ρ) hfinc
  haveI : Finite (MulAction.orbitRel.Quotient ↥Γ' (LT.LatticeTree.Vertex R₀ K₀)) := Finite.of_equiv Vd eV'
  haveI : Finite (MulAction.stabilizer ↥(Γc.map ρ) (LT.LatticeTree.stdVertex R₀ K₀)) := hfinV (LT.LatticeTree.stdVertex R₀ K₀)
  haveI hFI : Γ'.FiniteIndex := Skel.finiteIndex_of_finite_orbitQuotient_of_finite_stabilizer Γ' (LT.LatticeTree.stdVertex R₀ K₀)
  have hw₁ : ∀ e₁ : Ed, (Dd.w e₁ : ℕ) =
      Nat.card (MulAction.stabilizer ↥Γ' ((((eE' e₁).1).out : (BruhatTits.tree R₀ K₀).Dart))) := by
    intro e₁

    have h2 := heE' e₁
    obtain ⟨γ', hγ'⟩ : ∃ γ' : ↥Γ', γ' • ((ρ g)⁻¹ • (eEd.symm e₁).1.out) = ((eE' e₁).1).out :=
      Quotient.exact ((Quotient.out_eq ((eE' e₁).1)).trans h2)
    have hw := hDwd (eEd.symm e₁)
    rw [Equiv.apply_symm_apply] at hw
    rw [hw, ← Nat.card_congr (MulAction.stabilizerEquivStabilizer hγ'.symm).toEquiv]
    exact (Skel.card_stabilizer_inv_smul_eq (BruhatTits.tree R₀ K₀) (Γd.map ρ) (Γc.map ρ) (ρ g) Γ' hΓ' hHG₂ _).symm

  obtain ⟨ϖ₀, hϖ₀⟩ := IsDiscreteValuationRing.exists_irreducible R₀
  have hadj₀ : (BruhatTits.tree R₀ K₀).Adj (LT.LatticeTree.stdVertex R₀ K₀)
      (LT.LatticeTree.Vertex.act (LT.LatticeTree.diagSnd (LT.LatticeTree.unitOfNeZero (K := K₀) hϖ₀.ne_zero))
        (LT.LatticeTree.stdVertex R₀ K₀)) := by
    rw [BruhatTits.tree_adj_iff]
    refine ⟨(LT.LatticeTree.stdVertex_ne_act_diagSnd hϖ₀).symm, Or.inl ?_⟩
    exact ⟨_, _, LT.LatticeTree.isFullLattice_stdLattice,
      (LT.LatticeTree.isFullLattice_stdLattice).map _, rfl, by rw [LT.LatticeTree.stdVertex, LT.LatticeTree.Vertex.act_mk],
      LT.LatticeTree.adjacentLattice_stdLattice_diagSnd hϖ₀⟩
  let d₀ : (BruhatTits.tree R₀ K₀).Dart := ⟨(_, _), hadj₀⟩
  have hd₀ : Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) d₀.fst = 0 :=
    Mumford.vertexType_self _ _

  exact DegIdx.degTotal_eq_index (BruhatTits.tree R₀ K₀) Γ' hfinV
    (Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀)) hτc
    Dd eE' hw₁ Dc eEc.symm hw₂ μ hμE' d₀ hd₀

end S_CerednikDrinfeld_Mumford_finiteHom_degTotal_eq_index_of_mumfordQuotient_conj
end P2MW
export P2MW.S_CerednikDrinfeld_Mumford_finiteHom_degTotal_eq_index_of_mumfordQuotient_conj (solution)
