-- Prove2me | solution 1 for CerednikDrinfeld.Mumford.finiteHom_pullback_apply_eq_apply_transfer_of_forall_apply_eq_pathCycle_of_card_stabilizer
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/28b9015e-a4c0-540a-ac75-3012d539dee6

import Mathlib
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_AlgebraicCurve_TotallyDegenerateCovering_Hom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Mumford_finiteHom_pullback_apply_eq_apply_transfer_of_forall_apply_eq_pathCycle_of_card_stabilizer

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.Mumford MulAction
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

open NatOmegaBS NatOmegaPull NatOmegaPullW in
theorem solution
    {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
    (hT : 𝒯.IsTree) (hfin : ∀ w : W, Finite (stabilizer G w))
    (τ : W → ZMod 2) (hτ : ∀ (g : G) (w : W), τ (g • w) = τ w) (hadj : ∀ u v : W, 𝒯.Adj u v → τ u ≠ τ v)
    (Γ' : Subgroup G) [Γ'.FiniteIndex] [GraphAction ↥Γ' 𝒯]
    [DecidableEq (QuotEdge G 𝒯)] [DecidableEq (QuotEdge ↥Γ' 𝒯)]
    {E₁ V₁ : Type} [Fintype E₁] [Fintype V₁] [DecidableEq V₁] (D₁ : DegeneracyData E₁ V₁)
    (eE₁ : E₁ ≃ {e : QuotEdge ↥Γ' 𝒯 // τ e.out.fst = 0})
    (hw₁ : ∀ e₁ : E₁, (D₁.w e₁ : ℕ) = Nat.card (stabilizer ↥Γ' (((eE₁ e₁).1).out : 𝒯.Dart)))
    {E₂ V₂ : Type} [Fintype E₂] [DecidableEq E₂] [DecidableEq V₂] (D₂ : DegeneracyData E₂ V₂)
    (eE₂ : E₂ ≃ {e : QuotEdge G 𝒯 // τ e.out.fst = 0})
    (hw₂ : ∀ e₂ : E₂, (D₂.w e₂ : ℕ) = Nat.card (stabilizer G (((eE₂ e₂).1).out : 𝒯.Dart)))
    (μ : D₁.FiniteHom D₂)
    (hμE : ∀ e₁ : E₁, ((eE₂ (μ.mapE e₁)).1 : QuotEdge G 𝒯) = Quotient.mk (orbitRel G 𝒯.Dart) ((eE₁ e₁).1).out)
    (v₀ : W)
    (Φ₁ : Additive (Abelianization ↥Γ') →+ ↥(ribbonKernel D₁))
    (hΦ₁ : ∀ g : ↥Γ', (Φ₁ (Additive.ofMul (Abelianization.of g)) : E₁ → ℤ) = pathCycle 𝒯 (fun e => (eE₁ e).1) v₀ g)
    (Φ₂ : Additive (Abelianization G) →+ ↥(ribbonKernel D₂))
    (hΦ₂ : ∀ g : G, (Φ₂ (Additive.ofMul (Abelianization.of g)) : E₂ → ℤ) = pathCycle 𝒯 (fun e => (eE₂ e).1) v₀ g)
    (γ : G) :
    μ.pullback (Φ₂ (Additive.ofMul (Abelianization.of γ))) =
      Φ₁ (Additive.ofMul (MonoidHom.transfer (Abelianization.of : ↥Γ' →* Abelianization ↥Γ') γ)) := by
  classical
  haveI : Fintype (G ⧸ Γ') := Fintype.ofFinite _
  let s : G ⧸ Γ' → G := Quotient.out
  have hs : ∀ q : G ⧸ Γ', (QuotientGroup.mk (s q) : G ⧸ Γ') = q := fun q => Quotient.out_eq q
  obtain ⟨u, hu, htr⟩ := transfer_eq_prod_of_section Γ' (Abelianization.of : ↥Γ' →* Abelianization ↥Γ') s hs γ
  have hdegEq := deg_eq_relIndex 𝒯 Γ' hfin τ D₁ eE₁ hw₁ D₂ eE₂ hw₂ μ hμE
  rw [htr, map_ofMul_prod]
  apply Subtype.ext
  funext e₁
  rw [DegeneracyData.FiniteHom.pullback_apply, hΦ₂, Submodule.coe_sum, Finset.sum_apply]
  simp_rw [hΦ₁]

  set orb₁ : E₁ → QuotEdge ↥Γ' 𝒯 := fun e => (eE₁ e).1 with horb₁
  set orb₂ : E₂ → QuotEdge G 𝒯 := fun e => (eE₂ e).1 with horb₂
  let P : 𝒯.Path v₀ (γ • v₀) := BP.treePath 𝒯 hT v₀ (γ • v₀)
  rw [pathCycle_eq_walkCycle 𝒯 orb₂ hT.isAcyclic v₀ γ P]
  have hcomp : ∀ q : G ⧸ Γ', pathCycle 𝒯 orb₁ v₀ (u q) =
      BP.pot 𝒯 hT orb₁ v₀ ((s q)⁻¹ • γ • v₀) - BP.pot 𝒯 hT orb₁ v₀ ((s (γ⁻¹ • q))⁻¹ • v₀) := by
    intro q
    have key : ∀ (x : W), pathCycle 𝒯 orb₁ x (u q) =
        BP.pot 𝒯 hT orb₁ v₀ ((u q) • x) - BP.pot 𝒯 hT orb₁ v₀ x := by
      intro x
      rw [pathCycle_eq_walkCycle 𝒯 orb₁ hT.isAcyclic x (u q) (BP.treePath 𝒯 hT x ((u q) • x))]
      exact BP.walkCycle_eq_pot_sub_pot 𝒯 hT orb₁ v₀ _
    have hbase : pathCycle 𝒯 orb₁ v₀ (u q) = pathCycle 𝒯 orb₁ ((s (γ⁻¹ • q))⁻¹ • v₀) (u q) := by
      set xq : W := (s (γ⁻¹ • q))⁻¹ • v₀ with hxq
      have htrans := BP.walkCycle_eq_pot_sub_pot 𝒯 hT orb₁ v₀
        ((BP.treePath 𝒯 hT v₀ xq : 𝒯.Walk v₀ xq).map (smulHom (𝒯 := 𝒯) (u q)))
      rw [walkCycle_map_smulHom] at htrans
      change BP.pot 𝒯 hT orb₁ v₀ xq = _ at htrans
      simp only [smulHom_apply] at htrans
      rw [key, key, BP.pot_self, sub_zero, htrans]
      abel
    rw [hbase, key]
    congr 2
    show ((u q : ↥Γ') : G) • (s (γ⁻¹ • q))⁻¹ • v₀ = (s q)⁻¹ • γ • v₀
    rw [hu q, mul_smul, mul_smul, smul_inv_smul]
  simp_rw [hcomp]
  simp only [Pi.sub_apply]
  rw [Finset.sum_sub_distrib]
  have hre : ∑ q : G ⧸ Γ', BP.pot 𝒯 hT orb₁ v₀ ((s (γ⁻¹ • q))⁻¹ • v₀) e₁ =
      ∑ q : G ⧸ Γ', BP.pot 𝒯 hT orb₁ v₀ ((s q)⁻¹ • v₀) e₁ :=
    Fintype.sum_equiv (MulAction.toPerm (γ⁻¹ : G)) _ _ (fun q => rfl)
  rw [hre, ← Finset.sum_sub_distrib]
  have hsum : ∀ q : G ⧸ Γ', BP.pot 𝒯 hT orb₁ v₀ ((s q)⁻¹ • γ • v₀) e₁ - BP.pot 𝒯 hT orb₁ v₀ ((s q)⁻¹ • v₀) e₁ =
      ((P : 𝒯.Walk v₀ (γ • v₀)).darts.map fun d => dartIndex 𝒯 (orb₁ e₁) ((s q)⁻¹ • d)).sum := by
    intro q
    have h := BP.walkCycle_eq_pot_sub_pot 𝒯 hT orb₁ v₀ ((P : 𝒯.Walk v₀ (γ • v₀)).map (smulHom (𝒯 := 𝒯) (s q)⁻¹))
    simp only [smulHom_apply] at h
    have h' := congrFun h e₁
    simp only [Pi.sub_apply] at h'
    rw [← h']
    exact walkCycle_map_smulHom_apply 𝒯 Γ' orb₁ (s q)⁻¹ (P : 𝒯.Walk v₀ (γ • v₀)) e₁
  simp_rw [hsum]
  rw [sum_list_map_sum, hdegEq]
  simp only [walkCycle]
  rw [← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro d _
  have horb₂e : orb₂ (μ.mapE e₁) = Quotient.mk (orbitRel G 𝒯.Dart) ((eE₁ e₁).1).out := hμE e₁
  have horb₁e : orb₁ e₁ = Quotient.mk (orbitRel ↥Γ' 𝒯.Dart) ((eE₁ e₁).1).out := (Quotient.out_eq _).symm
  rw [horb₂e, horb₁e]
  simp only [dartIndex, Finset.sum_sub_distrib, mul_sub, mul_ite, mul_one, mul_zero]
  rw [sum_ite_mk_smul_eq_relIndex 𝒯 Γ' s hs _ d]
  congr 1
  calc (if (Quotient.mk (orbitRel G 𝒯.Dart) d.symm : QuotEdge G 𝒯) =
          Quotient.mk (orbitRel G 𝒯.Dart) ((eE₁ e₁).1).out then
          (Γ'.relIndex (stabilizer G ((eE₁ e₁).1).out) : ℤ) else 0)
      = ∑ q : G ⧸ Γ', if (Quotient.mk (orbitRel ↥Γ' 𝒯.Dart) ((s q)⁻¹ • d.symm) : QuotEdge ↥Γ' 𝒯) =
          Quotient.mk (orbitRel ↥Γ' 𝒯.Dart) ((eE₁ e₁).1).out then (1 : ℤ) else 0 :=
        (sum_ite_mk_smul_eq_relIndex 𝒯 Γ' s hs _ d.symm).symm
    _ = ∑ q : G ⧸ Γ', if (Quotient.mk (orbitRel ↥Γ' 𝒯.Dart) ((s q)⁻¹ • d).symm : QuotEdge ↥Γ' 𝒯) =
          Quotient.mk (orbitRel ↥Γ' 𝒯.Dart) ((eE₁ e₁).1).out then (1 : ℤ) else 0 :=
        Finset.sum_congr rfl fun q _ => if_congr (by rw [smul_dart_symm]) rfl rfl

end S_CerednikDrinfeld_Mumford_finiteHom_pullback_apply_eq_apply_transfer_of_forall_apply_eq_pathCycle_of_card_stabilizer
end P2MW
export P2MW.S_CerednikDrinfeld_Mumford_finiteHom_pullback_apply_eq_apply_transfer_of_forall_apply_eq_pathCycle_of_card_stabilizer (solution)
