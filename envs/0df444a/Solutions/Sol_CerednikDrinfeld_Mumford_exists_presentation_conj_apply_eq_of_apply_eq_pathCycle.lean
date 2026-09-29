-- Prove2me | solution 1 for CerednikDrinfeld.Mumford.exists_presentation_conj_apply_eq_of_apply_eq_pathCycle
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/7e666e5f-7ab4-5111-a679-3534e7bf9b6c

import Mathlib
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Mumford_exists_presentation_conj_apply_eq_of_apply_eq_pathCycle

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.Mumford MulAction

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

namespace ConjT

section Transport

variable {P : Type} [Group P]

theorem smul_H_eq (H : Subgroup P) (h : ↥H) {α : Type} [MulAction P α] (a : α) : h • a = (h : P) • a := rfl

theorem smul_Γ'_eq (G₂ : Subgroup P) (Γ' : Subgroup ↥G₂) (γ : ↥Γ') {α : Type} [MulAction P α] (a : α) :
    γ • a = ((γ : ↥G₂) : P) • a := rfl

def conjHom (H : Subgroup P) (p : P) (G₂ : Subgroup P) (Γ' : Subgroup ↥G₂)
    (hΓ' : ∀ x : ↥G₂, x ∈ Γ' ↔ p * (x : P) * p⁻¹ ∈ H) : ↥Γ' →* ↥H where
  toFun γ := ⟨p * ((γ : ↥G₂) : P) * p⁻¹, (hΓ' (γ : ↥G₂)).1 γ.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' γ δ := Subtype.ext (by
    simp only [Subgroup.coe_mul]
    group)

@[scoped simp] theorem conjHom_coe (H : Subgroup P) (p : P) (G₂ : Subgroup P) (Γ' : Subgroup ↥G₂)
    (hΓ' : ∀ x : ↥G₂, x ∈ Γ' ↔ p * (x : P) * p⁻¹ ∈ H) (γ : ↥Γ') :
    ((conjHom H p G₂ Γ' hΓ' γ : ↥H) : P) = p * ((γ : ↥G₂) : P) * p⁻¹ := rfl

def conjInv (H : Subgroup P) (p : P) (G₂ : Subgroup P) (Γ' : Subgroup ↥G₂)
    (hΓ' : ∀ x : ↥G₂, x ∈ Γ' ↔ p * (x : P) * p⁻¹ ∈ H)
    (hHG₂ : ∀ h : P, h ∈ H → p⁻¹ * h * p ∈ (G₂ : Subgroup P)) (h : ↥H) : ↥Γ' :=
  ⟨⟨p⁻¹ * (h : P) * p, hHG₂ h h.2⟩, (hΓ' _).2 (by
    have : p * (p⁻¹ * (h : P) * p) * p⁻¹ = h := by group
    rw [Subgroup.coe_mk, this]; exact h.2)⟩

@[scoped simp] theorem conjInv_coe (H : Subgroup P) (p : P) (G₂ : Subgroup P) (Γ' : Subgroup ↥G₂)
    (hΓ' : ∀ x : ↥G₂, x ∈ Γ' ↔ p * (x : P) * p⁻¹ ∈ H)
    (hHG₂ : ∀ h : P, h ∈ H → p⁻¹ * h * p ∈ (G₂ : Subgroup P)) (h : ↥H) :
    (((conjInv H p G₂ Γ' hΓ' hHG₂ h : ↥Γ') : ↥G₂) : P) = p⁻¹ * (h : P) * p := rfl

variable (H : Subgroup P) (p : P) (G₂ : Subgroup P) (Γ' : Subgroup ↥G₂)
    (hΓ' : ∀ x : ↥G₂, x ∈ Γ' ↔ p * (x : P) * p⁻¹ ∈ H)
    (hHG₂ : ∀ h : P, h ∈ H → p⁻¹ * h * p ∈ (G₂ : Subgroup P))

include hΓ' hHG₂ in

theorem mk_inv_smul_eq_of_rel {α : Type} [MulAction P α] {a b : α} (hab : (orbitRel ↥H α) a b) :
    (Quotient.mk (orbitRel ↥Γ' α) (p⁻¹ • a) : orbitRel.Quotient ↥Γ' α) = Quotient.mk _ (p⁻¹ • b) := by
  rw [orbitRel_apply, mem_orbit_iff] at hab
  obtain ⟨h, rfl⟩ := hab
  apply Quotient.sound
  change p⁻¹ • h • b ∈ orbit ↥Γ' (p⁻¹ • b)
  rw [mem_orbit_iff]
  refine ⟨conjInv H p G₂ Γ' hΓ' hHG₂ h, ?_⟩
  rw [smul_Γ'_eq, conjInv_coe, smul_H_eq, ← mul_smul, ← mul_smul]
  congr 1; group

include hΓ' in
theorem mk_smul_eq_of_rel {α : Type} [MulAction P α] {a b : α} (hab : (orbitRel ↥Γ' α) a b) :
    (Quotient.mk (orbitRel ↥H α) (p • a) : orbitRel.Quotient ↥H α) = Quotient.mk _ (p • b) := by
  rw [orbitRel_apply, mem_orbit_iff] at hab
  obtain ⟨γ, rfl⟩ := hab
  apply Quotient.sound
  change p • γ • b ∈ orbit ↥H (p • b)
  rw [mem_orbit_iff]
  refine ⟨conjHom H p G₂ Γ' hΓ' γ, ?_⟩
  rw [smul_H_eq, conjHom_coe, smul_Γ'_eq, ← mul_smul, ← mul_smul]
  congr 1; group

noncomputable def orbitEquiv (α : Type) [MulAction P α] : orbitRel.Quotient ↥H α ≃ orbitRel.Quotient ↥Γ' α where
  toFun := Quotient.lift (fun a => Quotient.mk (orbitRel ↥Γ' α) (p⁻¹ • a))
    (fun a b hab => mk_inv_smul_eq_of_rel H p G₂ Γ' hΓ' hHG₂ hab)
  invFun := Quotient.lift (fun a => Quotient.mk (orbitRel ↥H α) (p • a))
    (fun a b hab => mk_smul_eq_of_rel H p G₂ Γ' hΓ' hab)
  left_inv q := by
    induction q using Quotient.inductionOn with
    | h a =>
      show Quotient.mk (orbitRel ↥H α) (p • p⁻¹ • a) = Quotient.mk _ a
      rw [smul_inv_smul]
  right_inv q := by
    induction q using Quotient.inductionOn with
    | h a =>
      show Quotient.mk (orbitRel ↥Γ' α) (p⁻¹ • p • a) = Quotient.mk _ a
      rw [inv_smul_smul]

@[scoped simp] theorem orbitEquiv_mk (α : Type) [MulAction P α] (a : α) :
    orbitEquiv H p G₂ Γ' hΓ' hHG₂ α (Quotient.mk _ a) = Quotient.mk (orbitRel ↥Γ' α) (p⁻¹ • a) := rfl

@[scoped simp] theorem orbitEquiv_symm_mk (α : Type) [MulAction P α] (a : α) :
    (orbitEquiv H p G₂ Γ' hΓ' hHG₂ α).symm (Quotient.mk _ a) = Quotient.mk (orbitRel ↥H α) (p • a) := rfl

theorem orbitEquiv_eq_iff {α : Type} [MulAction P α] (q : orbitRel.Quotient ↥H α) (a : α) :
    orbitEquiv H p G₂ Γ' hΓ' hHG₂ α q = Quotient.mk (orbitRel ↥Γ' α) a ↔
      q = Quotient.mk (orbitRel ↥H α) (p • a) := by
  constructor
  · intro h
    have := congrArg (orbitEquiv H p G₂ Γ' hΓ' hHG₂ α).symm h
    rwa [Equiv.symm_apply_apply, orbitEquiv_symm_mk] at this
  · intro h
    rw [h, orbitEquiv_mk, inv_smul_smul]

theorem orbitEquiv_apply_eq (α : Type) [MulAction P α] (q : orbitRel.Quotient ↥H α) :
    orbitEquiv H p G₂ Γ' hΓ' hHG₂ α q = Quotient.mk (orbitRel ↥Γ' α) (p⁻¹ • q.out) := by
  conv_lhs => rw [← Quotient.out_eq q]
  rfl

end Transport

end ConjT
p2m_reactivate "P2MW.S_CerednikDrinfeld_Mumford_exists_presentation_conj_apply_eq_of_apply_eq_pathCycle.ConjT"

namespace ConjT

section Graph

variable {P : Type} [Group P] {W : Type} [MulAction P W] (𝒯 : SimpleGraph W) [GraphAction P 𝒯]
  (H : Subgroup P) [GraphAction ↥H 𝒯]

theorem walkCycle_map_smulHom_apply [DecidableEq (QuotEdge ↥H 𝒯)] {E : Type} (orb : E → QuotEdge ↥H 𝒯)
    (g : P) {u v : W} (w : 𝒯.Walk u v) (e : E) :
    walkCycle 𝒯 orb (w.map (smulHom (𝒯 := 𝒯) g)) e = (w.darts.map fun d => dartIndex 𝒯 (orb e) (g • d)).sum := by
  induction w with
  | nil => simp [walkCycle]
  | cons h p ih =>
    rw [SimpleGraph.Walk.map_cons, walkCycle_cons, ih, SimpleGraph.Walk.darts_cons, List.map_cons, List.sum_cons]
    rfl

theorem walkCycle_apply [DecidableEq (QuotEdge ↥H 𝒯)] {E : Type} (orb : E → QuotEdge ↥H 𝒯)
    {u v : W} (w : 𝒯.Walk u v) (e : E) :
    walkCycle 𝒯 orb w e = (w.darts.map fun d => dartIndex 𝒯 (orb e) d).sum := rfl

theorem mk_out_fst_eq (q : QuotEdge ↥H 𝒯) (d : 𝒯.Dart) (hq : q = Quotient.mk (orbitRel ↥H 𝒯.Dart) d) :
    (Quotient.mk (orbitRel ↥H W) q.out.fst : QuotVert ↥H W) = Quotient.mk (orbitRel ↥H W) d.fst := by
  subst hq
  have h : (orbitRel ↥H 𝒯.Dart) ((Quotient.mk (orbitRel ↥H 𝒯.Dart) d : QuotEdge ↥H 𝒯).out) d := Quotient.mk_out d
  rw [orbitRel_apply, mem_orbit_iff] at h
  obtain ⟨γ, hγ⟩ := h
  rw [← hγ, smul_dart_fst]
  exact Quotient.sound (mem_orbit _ γ)

theorem mk_out_snd_eq (q : QuotEdge ↥H 𝒯) (d : 𝒯.Dart) (hq : q = Quotient.mk (orbitRel ↥H 𝒯.Dart) d) :
    (Quotient.mk (orbitRel ↥H W) q.out.snd : QuotVert ↥H W) = Quotient.mk (orbitRel ↥H W) d.snd := by
  subst hq
  have h : (orbitRel ↥H 𝒯.Dart) ((Quotient.mk (orbitRel ↥H 𝒯.Dart) d : QuotEdge ↥H 𝒯).out) d := Quotient.mk_out d
  rw [orbitRel_apply, mem_orbit_iff] at h
  obtain ⟨γ, hγ⟩ := h
  rw [← hγ, smul_dart_snd]
  exact Quotient.sound (mem_orbit _ γ)

theorem tau_out_fst_eq (τ : W → ZMod 2) (hτ : ∀ (g : ↥H) (w : W), τ (g • w) = τ w) (d : 𝒯.Dart) :
    τ ((Quotient.mk (orbitRel ↥H 𝒯.Dart) d : QuotEdge ↥H 𝒯).out).fst = τ d.fst := by
  have h : (orbitRel ↥H 𝒯.Dart) ((Quotient.mk (orbitRel ↥H 𝒯.Dart) d : QuotEdge ↥H 𝒯).out) d := Quotient.mk_out d
  rw [orbitRel_apply, mem_orbit_iff] at h
  obtain ⟨g, hg⟩ := h
  rw [← hg, smul_dart_fst, hτ]

end Graph
p2m_reactivate "P2MW.S_CerednikDrinfeld_Mumford_exists_presentation_conj_apply_eq_of_apply_eq_pathCycle.ConjT"

end ConjT
p2m_reactivate "P2MW.S_CerednikDrinfeld_Mumford_exists_presentation_conj_apply_eq_of_apply_eq_pathCycle.ConjT"

open ConjT in
theorem solution
    {P : Type} [Group P] {W : Type} [MulAction P W] (𝒯 : SimpleGraph W) [GraphAction P 𝒯] (hT : 𝒯.IsTree)
    (τ : W → ZMod 2) (hadj : ∀ u v : W, 𝒯.Adj u v → τ u ≠ τ v)
    (H : Subgroup P) [GraphAction ↥H 𝒯] (hH : ∀ (h : ↥H) (w : W), τ (h • w) = τ w)
    (p : P) (hp : ∀ w : W, τ (p • w) = τ w)
    (G₂ : Subgroup P) [GraphAction ↥G₂ 𝒯] (hHG₂ : ∀ h : P, h ∈ H → p⁻¹ * h * p ∈ G₂)
    (Γ' : Subgroup ↥G₂) [GraphAction ↥Γ' 𝒯] (hΓ' : ∀ x : ↥G₂, x ∈ Γ' ↔ p * (x : P) * p⁻¹ ∈ H)
    [DecidableEq (QuotEdge ↥H 𝒯)] [DecidableEq (QuotEdge ↥Γ' 𝒯)]
    {E V : Type} [Fintype E] [DecidableEq V] (D : DegeneracyData E V)
    (eE : E ≃ {e : QuotEdge ↥H 𝒯 // τ e.out.fst = 0})
    (eV : V ≃ QuotVert ↥H W)
    (ha : ∀ e : E, eV (D.a e) = Quotient.mk (orbitRel ↥H W) (eE e).1.out.fst)
    (hb : ∀ e : E, eV (D.b e) = Quotient.mk (orbitRel ↥H W) (eE e).1.out.snd)
    (v₀ : W)
    (Φ : Additive (Abelianization ↥H) →+ ↥(ribbonKernel D))
    (hΦ : ∀ h : ↥H, (Φ (Additive.ofMul (Abelianization.of h)) : E → ℤ) = pathCycle 𝒯 (fun e => (eE e).1) v₀ h) :
    ∃ (eE' : E ≃ {e : QuotEdge ↥Γ' 𝒯 // τ e.out.fst = 0}) (eV' : V ≃ QuotVert ↥Γ' W)
      (Φ' : Additive (Abelianization ↥Γ') →+ ↥(ribbonKernel D)),
      (∀ e : E, ((eE' e).1 : QuotEdge ↥Γ' 𝒯) = Quotient.mk (orbitRel ↥Γ' 𝒯.Dart) (p⁻¹ • (eE e).1.out)) ∧
      (∀ v : V, ∀ w : W, eV v = Quotient.mk (orbitRel ↥H W) w → eV' v = Quotient.mk (orbitRel ↥Γ' W) (p⁻¹ • w)) ∧
      (∀ e : E, eV' (D.a e) = Quotient.mk (orbitRel ↥Γ' W) (eE' e).1.out.fst) ∧
      (∀ e : E, eV' (D.b e) = Quotient.mk (orbitRel ↥Γ' W) (eE' e).1.out.snd) ∧
      (∀ γ : ↥Γ', (Φ' (Additive.ofMul (Abelianization.of γ)) : E → ℤ) = pathCycle 𝒯 (fun e => (eE' e).1) v₀ γ) ∧
      (∀ γ : ↥Γ', Φ' (Additive.ofMul (Abelianization.of γ)) =
        Φ (Additive.ofMul (Abelianization.of (⟨p * ((γ : ↥G₂) : P) * p⁻¹, (hΓ' (γ : ↥G₂)).1 γ.2⟩ : ↥H)))) := by
  classical

  have hpinv : ∀ w : W, τ (p⁻¹ • w) = τ w := fun w => by
    have := hp (p⁻¹ • w); rw [smul_inv_smul] at this; exact this.symm
  have hΓτ : ∀ (γ : ↥Γ') (w : W), τ (γ • w) = τ w := by
    intro γ w
    have hmem : p * ((γ : ↥G₂) : P) * p⁻¹ ∈ H := (hΓ' (γ : ↥G₂)).1 γ.2
    have h1 := hH ⟨_, hmem⟩ (p • w)
    rw [smul_H_eq, ← mul_smul, show p * ((γ : ↥G₂) : P) * p⁻¹ * p = p * ((γ : ↥G₂) : P) by group,
      mul_smul, hp, hp] at h1
    rw [smul_Γ'_eq]
    exact h1

  let θE := orbitEquiv H p G₂ Γ' hΓ' hHG₂ 𝒯.Dart
  let θV := orbitEquiv H p G₂ Γ' hΓ' hHG₂ W
  have hθE : ∀ q : QuotEdge ↥H 𝒯, θE q = Quotient.mk (orbitRel ↥Γ' 𝒯.Dart) (p⁻¹ • q.out) :=
    fun q => orbitEquiv_apply_eq H p G₂ Γ' hΓ' hHG₂ 𝒯.Dart q

  have hcol : ∀ q : QuotEdge ↥H 𝒯, τ q.out.fst = 0 ↔ τ (θE q).out.fst = 0 := by
    intro q
    rw [hθE q, tau_out_fst_eq 𝒯 Γ' τ hΓτ, smul_dart_fst, hpinv]
  let eE' : E ≃ {e : QuotEdge ↥Γ' 𝒯 // τ e.out.fst = 0} := eE.trans (θE.subtypeEquiv hcol)
  let eV' : V ≃ QuotVert ↥Γ' W := eV.trans θV
  have heE' : ∀ e : E, ((eE' e).1 : QuotEdge ↥Γ' 𝒯) = Quotient.mk (orbitRel ↥Γ' 𝒯.Dart) (p⁻¹ • (eE e).1.out) :=
    fun e => hθE _

  let Φ' : Additive (Abelianization ↥Γ') →+ ↥(ribbonKernel D) :=
    Φ.comp (MonoidHom.toAdditive (Abelianization.map (conjHom H p G₂ Γ' hΓ')))
  have hΦ'6 : ∀ γ : ↥Γ', Φ' (Additive.ofMul (Abelianization.of γ)) =
      Φ (Additive.ofMul (Abelianization.of (⟨p * ((γ : ↥G₂) : P) * p⁻¹, (hΓ' (γ : ↥G₂)).1 γ.2⟩ : ↥H))) := by
    intro γ
    show Φ (Additive.ofMul (Abelianization.map (conjHom H p G₂ Γ' hΓ') (Abelianization.of γ))) = _
    rw [Abelianization.map_of]
    rfl
  refine ⟨eE', eV', Φ', heE', ?_, ?_, ?_, ?_, hΦ'6⟩
  ·
    intro v w hvw
    show θV (eV v) = _
    rw [hvw]
    rfl
  ·
    intro e
    show θV (eV (D.a e)) = _
    rw [ha, orbitEquiv_mk, ← smul_dart_fst, mk_out_fst_eq 𝒯 Γ' _ _ (heE' e)]
  ·
    intro e
    show θV (eV (D.b e)) = _
    rw [hb, orbitEquiv_mk, ← smul_dart_snd, mk_out_snd_eq 𝒯 Γ' _ _ (heE' e)]
  ·
    intro γ
    rw [hΦ'6, hΦ]
    set hγ : ↥H := ⟨p * ((γ : ↥G₂) : P) * p⁻¹, (hΓ' (γ : ↥G₂)).1 γ.2⟩ with hhγ
    set orbH : E → QuotEdge ↥H 𝒯 := fun e => (eE e).1 with horbH

    have keyH : ∀ (x : W) (h : ↥H), pathCycle 𝒯 orbH x h = BP.pot 𝒯 hT orbH v₀ (h • x) - BP.pot 𝒯 hT orbH v₀ x := by
      intro x h
      rw [pathCycle_eq_walkCycle 𝒯 orbH hT.isAcyclic x h (BP.treePath 𝒯 hT x (h • x))]
      exact BP.walkCycle_eq_pot_sub_pot 𝒯 hT orbH v₀ _
    have hbase : pathCycle 𝒯 orbH v₀ hγ = pathCycle 𝒯 orbH (p • v₀) hγ := by
      have htrans := BP.walkCycle_eq_pot_sub_pot 𝒯 hT orbH v₀
        ((BP.treePath 𝒯 hT v₀ (p • v₀) : 𝒯.Walk v₀ (p • v₀)).map (smulHom (𝒯 := 𝒯) hγ))
      rw [walkCycle_map_smulHom] at htrans
      change BP.pot 𝒯 hT orbH v₀ (p • v₀) = _ at htrans
      simp only [smulHom_apply] at htrans
      rw [keyH, keyH, BP.pot_self, sub_zero, htrans]
      abel
    rw [hbase, keyH]

    have hR : pathCycle 𝒯 (fun e => (eE' e).1) v₀ γ =
        walkCycle 𝒯 orbH ((BP.treePath 𝒯 hT v₀ (γ • v₀) : 𝒯.Walk v₀ (γ • v₀)).map (smulHom (𝒯 := 𝒯) p)) := by
      funext e
      rw [pathCycle_eq_walkCycle 𝒯 (fun e => (eE' e).1) hT.isAcyclic v₀ γ (BP.treePath 𝒯 hT v₀ (γ • v₀))]
      have hdart : ∀ d : 𝒯.Dart, dartIndex 𝒯 ((eE' e).1) d = dartIndex 𝒯 (orbH e) (p • d) := by
        intro d
        have h1 : ((eE' e).1 : QuotEdge ↥Γ' 𝒯) = θE (orbH e) := rfl
        simp only [dartIndex, h1]
        congr 1
        · exact if_congr ((eq_comm.trans (orbitEquiv_eq_iff H p G₂ Γ' hΓ' hHG₂ (orbH e) d)).trans eq_comm) rfl rfl
        · exact if_congr ((eq_comm.trans (orbitEquiv_eq_iff H p G₂ Γ' hΓ' hHG₂ (orbH e) d.symm)).trans
            (by rw [smul_dart_symm]; exact eq_comm)) rfl rfl
      rw [walkCycle_apply 𝒯 Γ', List.map_congr_left (fun d _ => hdart d)]
      exact (walkCycle_map_smulHom_apply 𝒯 H orbH p (BP.treePath 𝒯 hT v₀ (γ • v₀) : 𝒯.Walk v₀ (γ • v₀)) e).symm
    have hw := BP.walkCycle_eq_pot_sub_pot 𝒯 hT orbH v₀
      ((BP.treePath 𝒯 hT v₀ (γ • v₀) : 𝒯.Walk v₀ (γ • v₀)).map (smulHom (𝒯 := 𝒯) p))
    rw [hR, hw]
    simp only [smulHom_apply]
    congr 2

    rw [smul_H_eq, smul_Γ'_eq, ← mul_smul, ← mul_smul]
    congr 1
    simp only [hhγ]
    group

end S_CerednikDrinfeld_Mumford_exists_presentation_conj_apply_eq_of_apply_eq_pathCycle
end P2MW
export P2MW.S_CerednikDrinfeld_Mumford_exists_presentation_conj_apply_eq_of_apply_eq_pathCycle (solution)
