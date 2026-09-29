-- Prove2me | solution 1 for CerednikDrinfeld.QM.exists_eq_comp_autHom_of_comp_eq_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/fdca5720-73a0-502b-967c-524b9259ffb7

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Theorems.Thm_Algebra_IsInvariant_exists_ringHom_eq_comp_toRingHom_of_comp_algebraMap_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_exists_eq_comp_autHom_of_comp_eq_of_isAlgClosed

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

namespace GeoOrbit

theorem appLE_eq_of_eq {X Y : Scheme.{0}} {f₁ f₂ : X ⟶ Y} (h : f₁ = f₂) (U : Y.Opens) (V : X.Opens)
    (e₁ : V ≤ f₁ ⁻¹ᵁ U) (e₂ : V ≤ f₂ ⁻¹ᵁ U) : f₁.appLE U V e₁ = f₂.appLE U V e₂ := by
  subst h; rfl

theorem hom_eq_of_appLE_eq {T X : Scheme.{0}} [IsAffine T] (U : X.Opens) (hU : IsAffineOpen U) (x x' : T ⟶ X)
    (hx : ⊤ ≤ x ⁻¹ᵁ U) (hx' : ⊤ ≤ x' ⁻¹ᵁ U) (h : x.appLE U ⊤ hx = x'.appLE U ⊤ hx') : x = x' := by
  have e1 := IsAffineOpen.SpecMap_appLE_fromSpec x hU (isAffineOpen_top T) hx
  have e2 := IsAffineOpen.SpecMap_appLE_fromSpec x' hU (isAffineOpen_top T) hx'
  rw [IsAffineOpen.fromSpec_top] at e1 e2
  rw [← cancel_epi T.isoSpec.inv, ← e1, ← e2, h]

end GeoOrbit

open GeoOrbit in
theorem solution
    {M X : Scheme.{0}} {G : Type} [Group G] [Finite G] (ρ : G →* Aut M)
    (π : M ⟶ X) (hπ : ∀ g : G, (ρ g).hom ≫ π = π) (haff : IsAffineHom π)
    (hsec : ∀ V : X.Opens, Function.Injective (π.app V))
    (hinv : ∀ V : X.Opens, Set.range (π.app V) =
      {s | ∀ g : G, (ρ g).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπ g]) s = s})
    (k : Type) [Field k] [IsAlgClosed k] (x x' : Spec (CommRingCat.of k) ⟶ M) (h : x ≫ π = x' ≫ π) :
    ∃ g : G, x' = x ≫ (ρ g).hom := by
  classical

  let ξ : X := (x ≫ π).base (IsLocalRing.closedPoint k)
  obtain ⟨_, ⟨V, hV, rfl⟩, hξV, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ ξ) isOpen_univ
  let U : M.Opens := π ⁻¹ᵁ V
  have hU : IsAffineOpen U := hV.preimage π
  have hρU : ∀ g : G, U ≤ (ρ g).hom ⁻¹ᵁ U := fun g => by
    show π ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V)
    rw [← Scheme.Hom.comp_preimage, hπ g]
  have hpt : ∀ p : ↥(Spec (CommRingCat.of k)), p = IsLocalRing.closedPoint k := fun p => Subsingleton.elim _ _
  have hx : ⊤ ≤ x ⁻¹ᵁ U := by
    intro p _
    show (x ≫ π).base p ∈ V
    rw [hpt p]; exact hξV
  have hx' : ⊤ ≤ x' ⁻¹ᵁ U := by
    intro p _
    show (x' ≫ π).base p ∈ V
    rw [hpt p, ← h]; exact hξV

  let A : Type := Γ(X, V)
  let B : Type := Γ(M, U)
  let act : G → (B →+* B) := fun g => ((ρ g⁻¹).hom.appLE U U (hρU g⁻¹)).hom
  have act_apply : ∀ g (s : B), act g s = ((ρ g⁻¹).hom.appLE U U (hρU g⁻¹)) s := fun _ _ => rfl
  have act_one : ∀ s : B, act 1 s = s := by
    intro s
    have : (ρ (1 : G)⁻¹).hom.appLE U U (hρU 1⁻¹) = 𝟙 _ := by
      rw [appLE_eq_of_eq (f₂ := 𝟙 M) (by rw [inv_one, map_one]; rfl) U U _ le_rfl]
      have hmap : ∀ e : U ≤ U, M.presheaf.map (homOfLE e).op = 𝟙 _ := fun e => by
        rw [show homOfLE e = 𝟙 U from Subsingleton.elim _ _, op_id, CategoryTheory.Functor.map_id]
      simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp]
      first | exact hmap _ | (rw [Category.id_comp]; exact hmap _)
    show ((ρ (1 : G)⁻¹).hom.appLE U U (hρU 1⁻¹)).hom s = s
    rw [this]; rfl
  have act_mul : ∀ (g g' : G) (s : B), act (g * g') s = act g (act g' s) := by
    intro g g' s
    have hc : (ρ (g * g')⁻¹).hom = (ρ g⁻¹).hom ≫ (ρ g'⁻¹).hom := by
      rw [mul_inv_rev, map_mul]; rfl
    have : (ρ (g * g')⁻¹).hom.appLE U U (hρU (g * g')⁻¹) =
        (ρ g'⁻¹).hom.appLE U U (hρU g'⁻¹) ≫ (ρ g⁻¹).hom.appLE U U (hρU g⁻¹) := by
      rw [Scheme.Hom.appLE_comp_appLE]
      exact appLE_eq_of_eq hc U U _ _
    show ((ρ (g * g')⁻¹).hom.appLE U U _).hom s = ((ρ g⁻¹).hom.appLE U U _).hom (((ρ g'⁻¹).hom.appLE U U _).hom s)
    rw [this]; rfl
  letI instSMul : MulSemiringAction G B :=
    { smul := fun g s => act g s
      one_smul := fun s => act_one s
      mul_smul := fun g g' s => act_mul g g' s
      smul_zero := fun g => (act g).map_zero
      smul_add := fun g s t => (act g).map_add s t
      smul_one := fun g => (act g).map_one
      smul_mul := fun g s t => (act g).map_mul s t }
  letI instAlg : Algebra A B := (π.app V).hom.toAlgebra

  have hfix : ∀ (g : G) (a : A), act g ((π.app V).hom a) = (π.app V).hom a := by
    intro g a
    have : π.app V ≫ (ρ g⁻¹).hom.appLE U U (hρU g⁻¹) = π.app V := by
      rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
      exact appLE_eq_of_eq (hπ g⁻¹) V U _ _
    show ((ρ g⁻¹).hom.appLE U U _).hom ((π.app V).hom a) = (π.app V).hom a
    rw [← CommRingCat.comp_apply, this]
  haveI : SMulCommClass G A B := ⟨fun g a s => by
    show act g ((π.app V).hom a * s) = (π.app V).hom a * act g s
    rw [(act g).map_mul, hfix]⟩
  haveI : Algebra.IsInvariant A B G := ⟨fun s hs => by
    have hs' : s ∈ Set.range (π.app V) := by
      rw [hinv V]
      intro g
      have := hs g⁻¹
      change act g⁻¹ s = s at this
      simp only [act, inv_inv] at this
      exact this
    obtain ⟨a, ha⟩ := hs'
    exact ⟨a, ha⟩⟩

  let eK := Scheme.ΓSpecIso (CommRingCat.of k)
  let φ₁ : B →+* k := eK.hom.hom.comp (x.appLE U ⊤ hx).hom
  let φ₂ : B →+* k := eK.hom.hom.comp (x'.appLE U ⊤ hx').hom
  have hagree : φ₁.comp (algebraMap A B) = φ₂.comp (algebraMap A B) := by
    have e1 : π.app V ≫ x.appLE U ⊤ hx = (x ≫ π).appLE V ⊤ (by intro p _; show (x ≫ π).base p ∈ V; rw [hpt p]; exact hξV) := by
      rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    have e2 : π.app V ≫ x'.appLE U ⊤ hx' = (x' ≫ π).appLE V ⊤ (by intro p _; show (x' ≫ π).base p ∈ V; rw [hpt p, ← h]; exact hξV) := by
      rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    have e3 : π.app V ≫ x.appLE U ⊤ hx = π.app V ≫ x'.appLE U ⊤ hx' := by
      rw [e1, e2]; exact appLE_eq_of_eq h V ⊤ _ _
    ext a
    change (π.app V ≫ x.appLE U ⊤ hx ≫ eK.hom).hom a = (π.app V ≫ x'.appLE U ⊤ hx' ≫ eK.hom).hom a
    rw [← Category.assoc, e3, Category.assoc]
  obtain ⟨g₀, hg₀⟩ :=
    Algebra.IsInvariant.exists_ringHom_eq_comp_toRingHom_of_comp_algebraMap_eq G φ₁ φ₂ hagree

  refine ⟨g₀⁻¹, ?_⟩
  have hx'' : ⊤ ≤ (x ≫ (ρ g₀⁻¹).hom) ⁻¹ᵁ U := by
    intro p hp
    show (ρ g₀⁻¹).hom.base (x.base p) ∈ U
    exact hρU g₀⁻¹ (hx hp)
  apply hom_eq_of_appLE_eq U hU x' (x ≫ (ρ g₀⁻¹).hom) hx' hx''
  have e4 : (x ≫ (ρ g₀⁻¹).hom).appLE U ⊤ hx'' = (ρ g₀⁻¹).hom.appLE U U (hρU g₀⁻¹) ≫ x.appLE U ⊤ hx := by
    rw [Scheme.Hom.appLE_comp_appLE]
  rw [e4]
  haveI : Mono eK.hom := inferInstance
  rw [← cancel_mono eK.hom]
  ext s
  have := congrArg (fun ψ : B →+* k => ψ s) hg₀
  simp only [RingHom.comp_apply, MulSemiringAction.toRingHom_apply] at this
  change eK.hom.hom ((x'.appLE U ⊤ hx').hom s) = eK.hom.hom ((x.appLE U ⊤ hx).hom (act g₀ s)) at this
  show eK.hom.hom ((x'.appLE U ⊤ hx').hom s) = eK.hom.hom (((ρ g₀⁻¹).hom.appLE U U (hρU g₀⁻¹) ≫ x.appLE U ⊤ hx).hom s)
  rw [this]; rfl

end S_CerednikDrinfeld_QM_exists_eq_comp_autHom_of_comp_eq_of_isAlgClosed
end P2MW
export P2MW.S_CerednikDrinfeld_QM_exists_eq_comp_autHom_of_comp_eq_of_isAlgClosed (solution)
