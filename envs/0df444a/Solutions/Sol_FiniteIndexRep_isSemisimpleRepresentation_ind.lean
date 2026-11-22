-- Prove2me | solution 1 for FiniteIndexRep.isSemisimpleRepresentation_ind
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T20:00:31.072806+00:00
-- url     : https://prove2.me/submissions/e759a0e3-6ff1-41a8-9db7-70ffba8b77bd

import Mathlib
import Theorems.Thm_FiniteIndexRep_isSemisimpleRepresentation_iff_comp_subtype

set_option autoImplicit false

namespace Sol_FiniteIndexRep_isSemisimpleRepresentation_ind

open Representation

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- The defining relation of the induced representation: `⟦h g ⊗ σ(h) v⟧ = ⟦g ⊗ v⟧`. -/
lemma indV_mk_mul (H : Subgroup G) (σ : Representation k H V) (h : H) (g : G) (v : V) :
    IndV.mk H.subtype σ (h * g) (σ h v) = IndV.mk H.subtype σ g v := by
  have := Coinvariants.mk_self_apply
    (Representation.tprod ((leftRegular k G).comp H.subtype) σ) h
    (MonoidAlgebra.single g (1 : k) ⊗ₜ[k] v)
  simpa using this

/-- A `k`-submodule of the induced module containing all `⟦g ⊗ v⟧` is everything. -/
lemma indV_eq_top (H : Subgroup G) (σ : Representation k H V)
    (P : Submodule k (IndV H.subtype σ))
    (hP : ∀ g v, IndV.mk H.subtype σ g v ∈ P) : P = ⊤ := by
  have h0 : P.mkQ = 0 := by
    apply IndV.hom_ext
    intro g
    ext v
    simpa using (Submodule.Quotient.mk_eq_zero P).2 (hP g v)
  rw [← Submodule.ker_mkQ P, h0, LinearMap.ker_zero]


/-- Every `⟦g ⊗ v⟧` lies in the image of `⟦t ⊗ -⟧` for a coset representative `t` of `H g`. -/
lemma indV_mk_mem_range (H : Subgroup G) (σ : Representation k H V) (g : G) (v : V) :
    IndV.mk H.subtype σ g v ∈
      LinearMap.range (IndV.mk H.subtype σ ((QuotientGroup.mk g⁻¹ : G ⧸ H).out)⁻¹) := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g⁻¹
  refine ⟨σ h⁻¹ v, ?_⟩
  have e : ((QuotientGroup.mk g⁻¹ : G ⧸ H).out)⁻¹ = (h⁻¹ : H) * g := by
    rw [hh]; simp
  rw [e, ← indV_mk_mul H σ h ((h⁻¹ : H) * g) (σ h⁻¹ v)]
  congr 1
  · simp
  · rw [← Module.End.mul_apply, ← map_mul]; simp

/-- The induced module from a subgroup of finite index is finite-dimensional. -/
lemma finiteDimensional_indV (H : Subgroup G) [H.FiniteIndex] (σ : Representation k H V)
    [FiniteDimensional k V] : FiniteDimensional k (IndV H.subtype σ) := by
  let P : Submodule k (IndV H.subtype σ) :=
    ⨆ q : G ⧸ H, LinearMap.range (IndV.mk H.subtype σ (q.out)⁻¹)
  have hP : P = ⊤ := indV_eq_top H σ P fun g v =>
    (le_iSup (fun q : G ⧸ H => LinearMap.range (IndV.mk H.subtype σ (q.out)⁻¹)) _)
      (indV_mk_mem_range H σ g v)
  have : FiniteDimensional k P := inferInstance
  rw [hP] at this
  exact Module.Finite.equiv Submodule.topEquiv

/-- Conjugation by `g` maps the normal core of `H` into `H`. -/
def conjCore (H : Subgroup G) (g : G) : H.normalCore →* H where
  toFun n := ⟨g * n * g⁻¹, H.normalCore_le (H.normalCore_normal.conj_mem n n.2 g)⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [mul_assoc]

@[simp] lemma conjCore_coe (H : Subgroup G) (g : G) (n : H.normalCore) :
    ((conjCore H g n : H) : G) = g * n * g⁻¹ := rfl

/-- Two representations of possibly different monoids on the same space with the same sets of
operators have the same subrepresentations, hence are simultaneously semisimple. -/
lemma isSemisimpleRepresentation_of_same_operators {G₁ G₂ : Type*} [Monoid G₁] [Monoid G₂]
    (ρ₁ : Representation k G₁ V) (ρ₂ : Representation k G₂ V)
    (h₁₂ : ∀ a, ∃ b, ρ₁ a = ρ₂ b) (h₂₁ : ∀ b, ∃ a, ρ₂ b = ρ₁ a)
    (h : IsSemisimpleRepresentation ρ₂) : IsSemisimpleRepresentation ρ₁ := by
  let e : Subrepresentation ρ₁ ≃o Subrepresentation ρ₂ :=
    { toFun := fun W => ⟨W.toSubmodule, fun b v hv => by
        obtain ⟨a, ha⟩ := h₂₁ b; rw [ha]; exact W.apply_mem_toSubmodule a hv⟩
      invFun := fun W => ⟨W.toSubmodule, fun a v hv => by
        obtain ⟨b, hb⟩ := h₁₂ a; rw [hb]; exact W.apply_mem_toSubmodule b hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact e.complementedLattice_iff.2 h


/-- `v ↦ ⟦g ⊗ v⟧` intertwines `σ ∘ (n ↦ g n g⁻¹)` with the restriction of `Ind σ` to the
normal core of `H`. -/
noncomputable def indMkIntertwining (H : Subgroup G) (σ : Representation k H V) (g : G) :
    IntertwiningMap (σ.comp (conjCore H g)) ((ind H.subtype σ).comp H.normalCore.subtype) :=
  (IndV.mk H.subtype σ g).intertwiningMap_of_isIntertwiningMap _ _ fun n v => by
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype]
    rw [ind_mk, ← indV_mk_mul H σ (conjCore H g n) (g * (n : G)⁻¹) v]
    congr 1
    simp [mul_assoc]

/-- The conjugated restriction `σ ∘ (n ↦ g n g⁻¹)` is semisimple when the restriction of `σ` to the
normal core is. -/
lemma isSemisimple_comp_conjCore (H : Subgroup G) (σ : Representation k H V) (g : G)
    (h : IsSemisimpleRepresentation (σ.comp (H.normalCore.subgroupOf H).subtype)) :
    IsSemisimpleRepresentation (σ.comp (conjCore H g)) := by
  refine isSemisimpleRepresentation_of_same_operators _ _ (fun a => ?_) (fun b => ?_) h
  · refine ⟨⟨conjCore H g a, ?_⟩, rfl⟩
    rw [Subgroup.mem_subgroupOf, conjCore_coe]
    exact H.normalCore_normal.conj_mem a a.2 g
  · obtain ⟨⟨b, hb⟩, hb'⟩ := b
    rw [Subgroup.mem_subgroupOf] at hb'
    refine ⟨⟨g⁻¹ * b * g, by simpa using H.normalCore_normal.conj_mem b hb' g⁻¹⟩, ?_⟩
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype]
    congr 1
    ext
    simp [mul_assoc]

end Sol_FiniteIndexRep_isSemisimpleRepresentation_ind

open Representation Sol_FiniteIndexRep_isSemisimpleRepresentation_ind in
theorem solution {k G V : Type*} [Field k] [CharZero k] [Group G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V]
    (H : Subgroup G) [H.FiniteIndex] (σ : Representation k H V)
    (hσ : Representation.IsSemisimpleRepresentation σ) :
    Representation.IsSemisimpleRepresentation (Representation.ind H.subtype σ) := by
  classical
  have h1 : IsSemisimpleRepresentation (σ.comp (H.normalCore.subgroupOf H).subtype) :=
    (FiniteIndexRep.isSemisimpleRepresentation_iff_comp_subtype σ (H.normalCore.subgroupOf H)).1 hσ
  have : FiniteDimensional k (IndV H.subtype σ) := finiteDimensional_indV H σ
  rw [FiniteIndexRep.isSemisimpleRepresentation_iff_comp_subtype (ind H.subtype σ) H.normalCore,
    isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  let F : ∀ g : G, Representation.asModule (σ.comp (conjCore H g)) →ₗ[MonoidAlgebra k H.normalCore]
      Representation.asModule ((ind H.subtype σ).comp H.normalCore.subtype) := fun g =>
    IntertwiningMap.equivLinearMapAsModule _ _ (indMkIntertwining H σ g)
  refine isSemisimpleModule_of_isSemisimpleModule_submodule'
    (p := fun g : G => LinearMap.range (F g)) (fun g => ?_) ?_
  · have : IsSemisimpleModule (MonoidAlgebra k H.normalCore) (Representation.asModule (σ.comp (conjCore H g))) :=
      (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).1
        (isSemisimple_comp_conjCore H σ g h1)
    exact IsSemisimpleModule.range _
  · let ρN : Representation k H.normalCore (IndV H.subtype σ) :=
      (ind H.subtype σ).comp H.normalCore.subtype
    let S := ⨆ g : G, LinearMap.range (F g)
    have hS : (S.restrictScalars k).map ρN.asModuleEquiv.toLinearMap = ⊤ :=
      indV_eq_top H σ _ fun g v => by
        refine ⟨IndV.mk H.subtype σ g v, ?_, rfl⟩
        exact (le_iSup (fun g => LinearMap.range (F g)) g) ⟨v, rfl⟩
    rw [eq_top_iff]
    intro x _
    have hx : ρN.asModuleEquiv x ∈ (S.restrictScalars k).map ρN.asModuleEquiv.toLinearMap := by
      rw [hS]; exact Submodule.mem_top
    obtain ⟨y, hy, hxy⟩ := hx
    have hyx : y = x := ρN.asModuleEquiv.injective hxy
    rw [← hyx]
    exact hy
