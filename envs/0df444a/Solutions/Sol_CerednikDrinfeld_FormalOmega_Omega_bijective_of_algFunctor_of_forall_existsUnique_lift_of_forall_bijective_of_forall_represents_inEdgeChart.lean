-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.Omega.bijective_of_algFunctor_of_forall_existsUnique_lift_of_forall_bijective_of_forall_represents_inEdgeChart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/d999b6b2-fcc7-5aa0-8e35-9a9b4403c4e2

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_cover_pullback_map_inEdgeChart_stdEdge_line_eq
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_inEdgeChart_act_of_isPullback
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_edgeNondegAt_map_iff_edgeNondegAt_comap
import Theorems.Thm_CerednikDrinfeld_FormalOmega_Omega_existsUnique_glue_of_span_eq_top
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_existsUnique_algHom_chartERing_line_eq_and_natural_of_inEdgeChart
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_eq_of_inEdgeChart_of_line_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_nilpPoints_existsUnique_hom_comp_eq_and_forall_apply_eq_comp_of_natural
import Theorems.Thm_AlgebraicGeometry_Etale_of_forall_existsUnique_lift_of_isArtinianRing_of_isNoetherianRing
import Theorems.Thm_AlgebraicGeometry_UniversallyInjective_of_forall_isAlgClosed_points_eq
import Theorems.Thm_AlgebraicGeometry_isOpenImmersion_of_etale_of_universallyInjective
import Theorems.Thm_AlgebraicGeometry_locallyOfFinitePresentation_of_comp_eq_of_isLocallyNoetherian
import Theorems.Thm_CerednikDrinfeld_FormalOmega_Omega_exists_natural_injective_inEdgeChart_act_iff_spec_tensorProduct_chartERing
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_inEdgeChart_iff_of_isBaseChange_of_isLocalHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_Omega_bijective_of_algFunctor_of_forall_existsUnique_lift_of_forall_bijective_of_forall_represents_inEdgeChart
p2m_attr_erase "instance" "CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀"

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

noncomputable section

namespace P2mWs44OmegaPRLocal

open IsLocalRing

variable {𝒪 : Type} [CommRing 𝒪] (C : Type) [CommRing C] [Algebra 𝒪 C]

abbrev algO (B : Type) [CommRing B] [Algebra C B] : Algebra 𝒪 B :=
  ((algebraMap C B).comp (algebraMap 𝒪 C)).toAlgebra

theorem isScalarTower_algO (B : Type) [CommRing B] [Algebra C B] :
    letI : Algebra 𝒪 B := algO C B; IsScalarTower 𝒪 C B :=
  letI : Algebra 𝒪 B := algO C B
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

theorem algO_eq (B : Type) [CommRing B] [Algebra C B] (inst : Algebra 𝒪 B) [IsScalarTower 𝒪 C B] :
    inst = algO C B :=
  Algebra.algebra_ext _ _ fun r => by
    rw [IsScalarTower.algebraMap_apply 𝒪 C B r]; rfl

scoped instance finiteType_chartERing (π : 𝒪) (q : ℕ) : Algebra.FiniteType 𝒪 (chartERing 𝒪 π q) := by
  haveI : Algebra.FinitePresentation (edgeQuot 𝒪 π) (chartERing 𝒪 π q) :=
    IsLocalization.Away.finitePresentation (edgeQuot.discr 𝒪 π q)
  haveI : Algebra.FiniteType 𝒪 (edgeQuot 𝒪 π) :=
    Algebra.FiniteType.of_surjective (edgeQuot.mk 𝒪 π) Ideal.Quotient.mk_surjective
  exact Algebra.FiniteType.trans (S := edgeQuot 𝒪 π) inferInstance inferInstance

end P2mWs44OmegaPRLocal
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_Omega_bijective_of_algFunctor_of_forall_existsUnique_lift_of_forall_bijective_of_forall_represents_inEdgeChart.P2mWs44OmegaPRLocal"

open P2mWs44OmegaPRLocal

theorem R1bPort

    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (π : 𝒪) (hπ : Irreducible π) (q : ℕ) (hq : Nat.card (𝒪 ⧸ Ideal.span {π}) = q) [Finite (𝒪 ⧸ Ideal.span {π})]

    (C : Type) [CommRing C] [IsNoetherianRing C] [Algebra 𝒪 C] (hC : IsNilpotent (algebraMap 𝒪 C π))
    (X : Scheme.{0}) (fX : X ⟶ Spec (CommRingCat.of C)) [LocallyOfFiniteType fX]

    (θ : ∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S],
      (Scheme.nilpPoints fX).obj S → (Omega K₀ π).obj S)
    (hnat : ∀ (S S' : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
      [CommRing S'] [Algebra C S'] [IsNoetherianRing S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 C S']
      (g : S →ₐ[C] S') (x : (Scheme.nilpPoints fX).obj S),
      θ S' ((Scheme.nilpPoints fX).map g x) = (Omega K₀ π).map (g.restrictScalars 𝒪) (θ S x))

    (het : ∀ (S S₀ : Type) [CommRing S] [IsLocalRing S] [IsArtinianRing S] [IsAlgClosed (IsLocalRing.ResidueField S)]
      [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
      [CommRing S₀] [Nontrivial S₀] [Algebra C S₀] [IsNoetherianRing S₀] [Algebra 𝒪 S₀] [IsScalarTower 𝒪 C S₀]
      (p : S →ₐ[C] S₀), Function.Surjective p → (∀ s t : S, p s = 0 → p t = 0 → s * t = 0) →
      ∀ (x₀ : (Scheme.nilpPoints fX).obj S₀) (d : (Omega K₀ π).obj S),
        θ S₀ x₀ = (Omega K₀ π).map (p.restrictScalars 𝒪) d →
        ∃! x : (Scheme.nilpPoints fX).obj S, (Scheme.nilpPoints fX).map p x = x₀ ∧ θ S x = d)

    (hinjk : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra C k] [Algebra 𝒪 k] [IsScalarTower 𝒪 C k],
      Function.Injective (θ k))

    (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg : (g : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
    (γ : Matrix.GeneralLinearGroup (Fin 2) K₀)

    (ι : ∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S],
        (Scheme.nilpPoints (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : C →+* C ⊗[𝒪] chartERing 𝒪 π q)))).obj S → (Omega K₀ π).obj S)
    (hι :

      (∀ (S S' : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          [CommRing S'] [Algebra C S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 C S']
          (φ : S →ₐ[C] S') (y : (Scheme.nilpPoints (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : C →+* C ⊗[𝒪] chartERing 𝒪 π q)))).obj S),
          ι S' ((Scheme.nilpPoints (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : C →+* C ⊗[𝒪] chartERing 𝒪 π q)))).map φ y) =
            (Omega K₀ π).map (φ.restrictScalars 𝒪) (ι S y)) ∧

      (∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S], Function.Injective (ι S)) ∧

      (∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S] (d : (Omega K₀ π).obj S),
          DeligneDatum.InEdgeChart π d (FullLattice.act γ (FullLattice.act g (stdFullLattice K₀)))
            (FullLattice.act γ (stdFullLattice K₀)) ↔ ∃ y : (Scheme.nilpPoints (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : C →+* C ⊗[𝒪] chartERing 𝒪 π q)))).obj S, ι S y = d))

    (hin : ∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
      (x : (Scheme.nilpPoints fX).obj S),
      DeligneDatum.InEdgeChart π (θ S x) (FullLattice.act γ (FullLattice.act g (stdFullLattice K₀)))
        (FullLattice.act γ (stdFullLattice K₀))) :
    ∃ h : X ⟶ Spec (CommRingCat.of (C ⊗[𝒪] chartERing 𝒪 π q)),
      h ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : C →+* C ⊗[𝒪] chartERing 𝒪 π q)) = fX ∧
      IsOpenImmersion h ∧
      (∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          (x : (Scheme.nilpPoints fX).obj S)
          (y : (Scheme.nilpPoints (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : C →+* C ⊗[𝒪] chartERing 𝒪 π q)))).obj S),
          x.1 ≫ h = y.1 → θ S x = ι S y) := by
  classical
  obtain ⟨hιnat, hιinj, hιim⟩ := hι

  let R : Type := C ⊗[𝒪] chartERing 𝒪 π q
  let fY : Spec (CommRingCat.of (C ⊗[𝒪] chartERing 𝒪 π q)) ⟶ Spec (CommRingCat.of C) :=
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : C →+* C ⊗[𝒪] chartERing 𝒪 π q))

  let τ : ∀ (B : Type) [CommRing B] [Algebra C B] [IsNoetherianRing B],
      (Scheme.nilpPoints fX).obj B → (Scheme.nilpPoints fY).obj B :=
    fun B _ _ _ φ =>
      letI : Algebra 𝒪 B := algO C B
      haveI : IsScalarTower 𝒪 C B := isScalarTower_algO C B
      ((hιim B (θ B φ)).mp (hin B φ)).choose
  have hτ : ∀ (B : Type) [CommRing B] [Algebra C B] [IsNoetherianRing B] (φ : (Scheme.nilpPoints fX).obj B),
      @ι B _ _ (algO C B) (isScalarTower_algO C B) (τ B φ) =
        @θ B _ _ _ (algO C B) (isScalarTower_algO C B) φ := by
    intro B _ _ _ φ
    letI : Algebra 𝒪 B := algO C B
    haveI : IsScalarTower 𝒪 C B := isScalarTower_algO C B
    exact ((hιim B (θ B φ)).mp (hin B φ)).choose_spec
  have hτnat : ∀ (B B' : Type) [CommRing B] [Algebra C B] [IsNoetherianRing B] [CommRing B'] [Algebra C B']
      [IsNoetherianRing B'] (f : B →ₐ[C] B') (φ : (Scheme.nilpPoints fX).obj B),
      τ B' ((Scheme.nilpPoints fX).map f φ) = (Scheme.nilpPoints fY).map f (τ B φ) := by
    intro B B' _ _ _ _ _ _ f φ
    letI : Algebra 𝒪 B := algO C B
    haveI : IsScalarTower 𝒪 C B := isScalarTower_algO C B
    letI : Algebra 𝒪 B' := algO C B'
    haveI : IsScalarTower 𝒪 C B' := isScalarTower_algO C B'
    apply hιinj B'
    rw [hτ, hιnat, hτ, ← hnat]

  obtain ⟨h, ⟨hcomm, hh⟩, -⟩ :=
    AlgebraicGeometry.Scheme.nilpPoints.existsUnique_hom_comp_eq_and_forall_apply_eq_comp_of_natural
      (𝒪 := C) fX fY τ hτnat
  have hcomm' : h ≫ fY = fX := hcomm

  have hcompat : ∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S]
      (x : (Scheme.nilpPoints fX).obj S) (y : (Scheme.nilpPoints fY).obj S),
      x.1 ≫ h = y.1 →
        @θ S _ _ _ (algO C S) (isScalarTower_algO C S) x = @ι S _ _ (algO C S) (isScalarTower_algO C S) y := by
    intro S _ _ _ x y hy
    have e2 : τ S x = y := Subtype.ext (by rw [hh S x]; exact hy)
    rw [← e2, hτ]

  have hYpt : ∀ (S : Type) [CommRing S] [Algebra C S] (x' : Spec (CommRingCat.of S) ⟶ X),
      x' ≫ fX = Scheme.specOver S → (x' ≫ h) ≫ fY = Scheme.specOver S := by
    intro S _ _ x' hx'
    rw [Category.assoc, hcomm]; exact hx'
  refine ⟨h, hcomm, ?_, ?_⟩
  swap
  · intro S _ _ _ inst𝒪 instT x y hy
    have e := algO_eq C S inst𝒪
    subst e
    exact hcompat S x y hy

  haveI : IsNoetherianRing (C ⊗[𝒪] chartERing 𝒪 π q) :=
    Algebra.FiniteType.isNoetherianRing C (C ⊗[𝒪] chartERing 𝒪 π q)
  haveI : LocallyOfFiniteType fY :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr (inferInstance : Algebra.FiniteType C (C ⊗[𝒪] chartERing 𝒪 π q)))
  haveI : LocallyOfFinitePresentation h :=
    AlgebraicGeometry.locallyOfFinitePresentation_of_comp_eq_of_isLocallyNoetherian fX fY h hcomm
  haveI hEt : Etale h := by
    apply AlgebraicGeometry.Etale.of_forall_existsUnique_lift_of_isArtinianRing_of_isNoetherianRing
      (R := C ⊗[𝒪] chartERing 𝒪 π q) h
    intro T' T _ _ _ _ _ _ p hp hker s m hsm

    let ψ : C ⊗[𝒪] chartERing 𝒪 π q →+* T' := (Spec.preimage s).hom
    have hψ : Spec.map (CommRingCat.ofHom ψ) = s := by
      show Spec.map (CommRingCat.ofHom (Spec.preimage s).hom) = s
      rw [CommRingCat.ofHom_hom, Spec.map_preimage]
    letI instCT' : Algebra C T' := (ψ.comp Algebra.TensorProduct.includeLeftRingHom).toAlgebra
    letI instCT : Algebra C T := (p.comp (algebraMap C T')).toAlgebra
    letI : Algebra 𝒪 T' := algO C T'
    haveI : IsScalarTower 𝒪 C T' := isScalarTower_algO C T'
    letI : Algebra 𝒪 T := algO C T
    haveI : IsScalarTower 𝒪 C T := isScalarTower_algO C T
    haveI : IsNoetherianRing T := isNoetherianRing_of_surjective T' T p hp
    let p' : T' →ₐ[C] T := ⟨p, fun _ => rfl⟩
    have hp' : (p' : T' →+* T) = p := rfl
    have hsT' : Scheme.specOver (𝒪 := C) T' = s ≫ fY := by
      show Spec.map (CommRingCat.ofHom (ψ.comp Algebra.TensorProduct.includeLeftRingHom)) = s ≫ fY
      rw [CommRingCat.ofHom_comp, Spec.map_comp, hψ]
    have hsT : Scheme.specOver (𝒪 := C) T = Spec.map (CommRingCat.ofHom p) ≫ s ≫ fY := by
      rw [← hsT', ← Scheme.specMap_algHom_comp_specOver p']

    let ys : (Scheme.nilpPoints fY).obj T' := ⟨s, hsT'.symm⟩
    let x₀ : (Scheme.nilpPoints fX).obj T := ⟨m, by
      rw [← hcomm', ← Category.assoc, hsm, Category.assoc, hsT]⟩

    have hθ₀ : θ T x₀ = (Omega K₀ π).map (p'.restrictScalars 𝒪) (ι T' ys) := by
      have := hcompat T x₀ ((Scheme.nilpPoints fY).map p' ys) (by
        show m ≫ h = Spec.map (CommRingCat.ofHom (p' : T' →+* T)) ≫ s; rw [hp']; exact hsm)
      rw [this, hιnat]

    have hker' : ∀ a b : T', p' a = 0 → p' b = 0 → a * b = 0 := by
      intro a b ha hb
      have hle : RingHom.ker p ≤ IsLocalRing.maximalIdeal T' := IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top p)
      have : a * b ∈ RingHom.ker p * IsLocalRing.maximalIdeal T' :=
        Ideal.mul_mem_mul ((RingHom.mem_ker).mpr ha) (hle ((RingHom.mem_ker).mpr hb))
      rwa [hker, Ideal.mem_bot] at this

    obtain ⟨x, ⟨hx₀, hxd⟩, huniq⟩ := het T' T p' hp hker' x₀ (ι T' ys) hθ₀
    have hm'Y : (x.1 ≫ h) ≫ fY = Scheme.specOver T' := hYpt T' x.1 x.2
    have hm's : x.1 ≫ h = s := by
      have := hcompat T' x ⟨x.1 ≫ h, hm'Y⟩ rfl
      rw [hxd] at this
      exact congrArg Subtype.val (hιinj T' this).symm
    refine ⟨x.1, ⟨hm's, ?_⟩, ?_⟩
    · have := congrArg Subtype.val hx₀
      simpa only [Scheme.nilpPoints_map_val, hp'] using this
    · rintro m'' ⟨hm''s, hm''p⟩
      let x'' : (Scheme.nilpPoints fX).obj T' := ⟨m'', by
        rw [← hcomm', ← Category.assoc, hm''s]; exact hsT'.symm⟩
      have h1 : (Scheme.nilpPoints fX).map p' x'' = x₀ := by
        apply Subtype.ext
        show Spec.map (CommRingCat.ofHom (p' : T' →+* T)) ≫ m'' = m
        rw [hp', hm''p]
      have h2 : θ T' x'' = ι T' ys := by
        have := hcompat T' x'' ⟨m'' ≫ h, hYpt T' m'' x''.2⟩ rfl
        rw [this]
        congr 1
        exact Subtype.ext hm''s
      have h3 : x'' = x := huniq x'' ⟨h1, h2⟩
      exact congrArg Subtype.val h3
  haveI hUI : UniversallyInjective h := by
    apply AlgebraicGeometry.UniversallyInjective.of_forall_isAlgClosed_points_eq
    intro k _ _ a b hab
    let ψ : C →+* k := (Spec.preimage (a ≫ fX)).hom
    letI : Algebra C k := ψ.toAlgebra
    letI : Algebra 𝒪 k := algO C k
    haveI : IsScalarTower 𝒪 C k := isScalarTower_algO C k
    have hsp : Scheme.specOver (𝒪 := C) k = a ≫ fX := by
      show Spec.map (CommRingCat.ofHom (Spec.preimage (a ≫ fX)).hom) = _
      rw [CommRingCat.ofHom_hom, Spec.map_preimage]
    let xa : (Scheme.nilpPoints fX).obj k := ⟨a, hsp.symm⟩
    let xb : (Scheme.nilpPoints fX).obj k := ⟨b, by
      rw [hsp, ← hcomm', ← Category.assoc, ← hab, Category.assoc]⟩
    have hya : (a ≫ h) ≫ fY = Scheme.specOver k := hYpt k a xa.2
    have : θ k xa = θ k xb := by
      rw [hcompat k xa ⟨a ≫ h, hya⟩ rfl, hcompat k xb ⟨a ≫ h, hya⟩ hab.symm]
    exact congrArg Subtype.val (hinjk k this)
  exact AlgebraicGeometry.isOpenImmersion_of_etale_of_universallyInjective h

open P2mWs44OmegaPRLocal in

theorem p7_local

    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (π : 𝒪) (hπ : Irreducible π) (q : ℕ) (hq : Nat.card (𝒪 ⧸ Ideal.span {π}) = q) [Finite (𝒪 ⧸ Ideal.span {π})]

    (C : Type) [CommRing C] [IsNoetherianRing C] [Algebra 𝒪 C] (hC : IsNilpotent (algebraMap 𝒪 C π))

    (PR : AlgFunctor C)

    (θ : ∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S],
      PR.obj S → (Omega K₀ π).obj S)
    (hnat : ∀ (S S' : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
      [CommRing S'] [Algebra C S'] [IsNoetherianRing S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 C S']
      (φ : S →ₐ[C] S') (x : PR.obj S),
      θ S' (PR.map φ x) = (Omega K₀ π).map (φ.restrictScalars 𝒪) (θ S x))

    (het : ∀ (S S₀ : Type) [CommRing S] [IsLocalRing S] [IsArtinianRing S] [IsAlgClosed (IsLocalRing.ResidueField S)]
      [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
      [CommRing S₀] [Nontrivial S₀] [Algebra C S₀] [IsNoetherianRing S₀] [Algebra 𝒪 S₀] [IsScalarTower 𝒪 C S₀]
      (p : S →ₐ[C] S₀), Function.Surjective p → (∀ s t : S, p s = 0 → p t = 0 → s * t = 0) →
      ∀ (x₀ : PR.obj S₀) (d : (Omega K₀ π).obj S),
        θ S₀ x₀ = (Omega K₀ π).map (p.restrictScalars 𝒪) d →
        ∃! x : PR.obj S, PR.map p x = x₀ ∧ θ S x = d)

    (hpts : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra C k] [Algebra 𝒪 k] [IsScalarTower 𝒪 C k],
      Function.Bijective (θ k))

    (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg : (g : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])

    (hrep : ∀ γ : Matrix.GeneralLinearGroup (Fin 2) K₀,
      ∃ (X : Scheme.{0}) (fX : X ⟶ Spec (CommRingCat.of C)) (_ : LocallyOfFiniteType fX)
        (e : ∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S],
          (Scheme.nilpPoints fX).obj S → PR.obj S),

        (∀ (S S' : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
            [CommRing S'] [Algebra C S'] [IsNoetherianRing S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 C S'] (φ : S →ₐ[C] S')
            (y : (Scheme.nilpPoints fX).obj S)
            (y' : (Scheme.nilpPoints fX).obj S'),
            y'.1 = Spec.map (CommRingCat.ofHom (φ : S →+* S')) ≫ y.1 → e S' y' = PR.map φ (e S y)) ∧

        (∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
            (y y' : (Scheme.nilpPoints fX).obj S), e S y = e S y' → y = y') ∧

        (∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S] (x : PR.obj S),
            (∃ y : (Scheme.nilpPoints fX).obj S, e S y = x) ↔
              DeligneDatum.InEdgeChart π (θ S x) (FullLattice.act γ (FullLattice.act g (stdFullLattice K₀)))
                (FullLattice.act γ (stdFullLattice K₀))))  :
    ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K₀)
      (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
      (d : (Omega K₀ π).obj S),
      DeligneDatum.InEdgeChart π d (FullLattice.act γ (FullLattice.act g (stdFullLattice K₀))) (FullLattice.act γ (stdFullLattice K₀)) →
      ∃! x : PR.obj S, θ S x = d := by
  classical
  intro γ S _ _ _ _ _ d hd
  obtain ⟨X, fX, hlft, e, henat, heinj, heimg⟩ := hrep γ
  haveI := hlft

  obtain ⟨ι, hιnat, hιinj, hιim⟩ :=
    CerednikDrinfeld.FormalOmega.Omega.exists_natural_injective_inEdgeChart_act_iff_spec_tensorProduct_chartERing π hπ q hq C hC g hg γ

  have hnatγ : ∀ (S S' : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
      [CommRing S'] [Algebra C S'] [IsNoetherianRing S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 C S']
      (φ : S →ₐ[C] S') (y : (Scheme.nilpPoints fX).obj S),
      θ S' (e S' ((Scheme.nilpPoints fX).map φ y)) = (Omega K₀ π).map (φ.restrictScalars 𝒪) (θ S (e S y)) := by
    intro S S' _ _ _ _ _ _ _ _ _ _ φ y
    rw [henat S S' φ y ((Scheme.nilpPoints fX).map φ y) rfl, hnat]
  have hinγ : ∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
      (y : (Scheme.nilpPoints fX).obj S), DeligneDatum.InEdgeChart π (θ S (e S y)) (FullLattice.act γ (FullLattice.act g (stdFullLattice K₀))) (FullLattice.act γ (stdFullLattice K₀)) :=
    fun S _ _ _ _ _ y => (heimg S (e S y)).mp ⟨y, rfl⟩
  have hinjγ : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra C k] [Algebra 𝒪 k] [IsScalarTower 𝒪 C k],
      Function.Injective (fun y : (Scheme.nilpPoints fX).obj k => θ k (e k y)) :=
    fun k _ _ _ _ _ y y' hyy => heinj k y y' ((hpts k).1 hyy)
  have hetγ : ∀ (S S₀ : Type) [CommRing S] [IsLocalRing S] [IsArtinianRing S] [IsAlgClosed (IsLocalRing.ResidueField S)]
      [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
      [CommRing S₀] [Nontrivial S₀] [Algebra C S₀] [IsNoetherianRing S₀] [Algebra 𝒪 S₀] [IsScalarTower 𝒪 C S₀]
      (p : S →ₐ[C] S₀), Function.Surjective p → (∀ s t : S, p s = 0 → p t = 0 → s * t = 0) →
      ∀ (x₀ : (Scheme.nilpPoints fX).obj S₀) (d : (Omega K₀ π).obj S),
        θ S₀ (e S₀ x₀) = (Omega K₀ π).map (p.restrictScalars 𝒪) d →
        ∃! x : (Scheme.nilpPoints fX).obj S, (Scheme.nilpPoints fX).map p x = x₀ ∧ θ S (e S x) = d := by
    intro S S₀ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p hp hsq x₀ d hx₀

    obtain ⟨z, ⟨hz₀, hzd⟩, hzu⟩ := het S S₀ p hp hsq (e S₀ x₀) d hx₀

    haveI : IsLocalRing S₀ := IsLocalRing.of_surjective' (p : S →+* S₀) hp
    haveI : IsLocalHom (p.restrictScalars 𝒪 : S →ₐ[𝒪] S₀) :=
      ⟨fun a ha => (hp.isLocalHom (p : S →+* S₀)).map_nonunit a ha⟩
    have hdch : DeligneDatum.InEdgeChart π d (FullLattice.act γ (FullLattice.act g (stdFullLattice K₀))) (FullLattice.act γ (stdFullLattice K₀)) := by
      have hbc := (CerednikDrinfeld.FormalOmega.DeligneDatum.inEdgeChart_iff_of_isBaseChange_of_isLocalHom π
        (p.restrictScalars 𝒪) d ((Omega K₀ π).map (p.restrictScalars 𝒪) d)
        (DeligneDatum.isBaseChange_map π (p.restrictScalars 𝒪) d)
        (FullLattice.act γ (FullLattice.act g (stdFullLattice K₀))) (FullLattice.act γ (stdFullLattice K₀))).mp
      apply hbc
      rw [← hx₀]
      exact hinγ S₀ x₀

    obtain ⟨x, hx⟩ := (heimg S z).mpr (by rw [hzd]; exact hdch)
    refine ⟨x, ⟨?_, by rw [hx]; exact hzd⟩, ?_⟩
    · apply heinj S₀
      rw [henat S S₀ p x ((Scheme.nilpPoints fX).map p x) rfl, hx, hz₀]
    · rintro x' ⟨hx'₀, hx'd⟩
      apply heinj S
      rw [hx]
      apply hzu
      exact ⟨by rw [← henat S S₀ p x' ((Scheme.nilpPoints fX).map p x') rfl, hx'₀], hx'd⟩

  obtain ⟨h, hcomm, hopen, hθι⟩ := R1bPort π hπ q hq C hC X fX (fun S _ _ _ _ _ y => θ S (e S y)) hnatγ hetγ hinjγ g hg γ ι
    ⟨hιnat, hιinj, hιim⟩ hinγ
  haveI := hopen
  have hYpt : ∀ (T : Type) [CommRing T] [Algebra C T] (x' : Spec (CommRingCat.of T) ⟶ X),
      x' ≫ fX = Scheme.specOver T → (x' ≫ h) ≫ (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : C →+* C ⊗[𝒪] chartERing 𝒪 π q))) = Scheme.specOver T := by
    intro T _ _ x' hx'
    rw [Category.assoc, hcomm]; exact hx'

  obtain ⟨y, hy⟩ := (hιim S d).1 hd
  have hrange : Set.range ⇑y.1 ⊆ Set.range ⇑h := by
    rintro _ ⟨pnt, rfl⟩
    let κ : Type := pnt.asIdeal.ResidueField
    let k : Type := AlgebraicClosure κ
    let ψr : S →+* k := algebraMap S k
    have hψr : ψr = (algebraMap κ k).comp (algebraMap S κ) := IsScalarTower.algebraMap_eq S κ k
    let ψ : S →ₐ[C] k := IsScalarTower.toAlgHom C S k
    let yk : (Scheme.nilpPoints (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : C →+* C ⊗[𝒪] chartERing 𝒪 π q)))).obj k := (Scheme.nilpPoints (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : C →+* C ⊗[𝒪] chartERing 𝒪 π q)))).map ψ y
    let dk : (Omega K₀ π).obj k := (Omega K₀ π).map (ψ.restrictScalars 𝒪) d
    have hyk : ι k yk = dk := by rw [hιnat, hy]
    obtain ⟨xk, hxk⟩ := (hpts k).2 dk
    have hInk : DeligneDatum.InEdgeChart π dk (FullLattice.act γ (FullLattice.act g (stdFullLattice K₀))) (FullLattice.act γ (stdFullLattice K₀)) := (hιim k dk).2 ⟨yk, hyk⟩
    obtain ⟨xk', hxk'⟩ := (heimg k xk).mpr (by rw [hxk]; exact hInk)
    let yk' : (Scheme.nilpPoints (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : C →+* C ⊗[𝒪] chartERing 𝒪 π q)))).obj k := ⟨xk'.1 ≫ h, hYpt k xk'.1 xk'.2⟩
    have hyk' : yk' = yk := hιinj k ((hθι k xk' yk' rfl).symm.trans (by rw [hxk', hxk, hyk]))

    let pt : PrimeSpectrum k := ⟨⊥, Ideal.isPrime_bot⟩
    have hpt : (Spec.map (CommRingCat.ofHom ψr)) pt = pnt := by
      apply PrimeSpectrum.ext
      show Ideal.comap ψr ⊥ = pnt.asIdeal
      rw [← RingHom.ker_eq_comap_bot, hψr,
        ← RingHom.comap_ker, (RingHom.injective_iff_ker_eq_bot _).1 (algebraMap κ k).injective,
        ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]
    refine ⟨xk'.1 pt, ?_⟩
    have e1 : (xk'.1 ≫ h) pt = yk.1 pt := by rw [← hyk']
    rw [Scheme.Hom.comp_apply] at e1
    rw [e1]
    show (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ y.1) pt = y.1 pnt
    rw [Scheme.Hom.comp_apply]
    exact congrArg _ hpt
  let x' : Spec (CommRingCat.of S) ⟶ X := IsOpenImmersion.lift h y.1 hrange
  have hx' : x' ≫ h = y.1 := IsOpenImmersion.lift_fac _ _ _
  let xr : (Scheme.nilpPoints fX).obj S := ⟨x', by rw [← hcomm, ← Category.assoc, hx']; exact y.2⟩
  have hxr : θ S (e S xr) = d := by
    rw [hθι S xr ⟨x' ≫ h, by rw [Category.assoc, hcomm]; exact xr.2⟩ rfl, ← hy]
    congr 1
    exact Subtype.ext hx'

  refine ⟨e S xr, hxr, ?_⟩
  intro x₁ hx₁
  obtain ⟨y₁, rfl⟩ := (heimg S x₁).mpr (by rw [hx₁]; exact hd)
  congr 1
  have hz : (⟨y₁.1 ≫ h, hYpt S y₁.1 y₁.2⟩ : (Scheme.nilpPoints (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : C →+* C ⊗[𝒪] chartERing 𝒪 π q)))).obj S) = ⟨xr.1 ≫ h, hYpt S xr.1 xr.2⟩ :=
    hιinj S (by rw [← hθι S y₁ _ rfl, ← hθι S xr _ rfl, hx₁, hxr])
  have := congrArg Subtype.val hz
  exact Subtype.ext ((cancel_mono h).mp this)

theorem solution

    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (π : 𝒪) (hπ : Irreducible π) (q : ℕ) (hq : Nat.card (𝒪 ⧸ Ideal.span {π}) = q) [Finite (𝒪 ⧸ Ideal.span {π})]

    (C : Type) [CommRing C] [IsNoetherianRing C] [Algebra 𝒪 C] (hC : IsNilpotent (algebraMap 𝒪 C π))

    (PR : AlgFunctor C)
    (hsheaf : ∀ (A : Type) [CommRing A] [Algebra C A] (n : ℕ) (f : Fin n → A),
      Ideal.span (Set.range f) = ⊤ →
      ∀ (B : Fin n → Type) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)] [∀ i, Algebra C (B i)]
        [∀ i, IsScalarTower C A (B i)] [∀ i, IsLocalization.Away (f i) (B i)] (s : ∀ i, PR.obj (B i)),
      (∀ (i j : Fin n) (D : Type) [CommRing D] [Algebra A D] [Algebra C D] [IsScalarTower C A D]
          [IsLocalization.Away (f i * f j) D] (ρ₁ : B i →ₐ[A] D) (ρ₂ : B j →ₐ[A] D),
          PR.map (ρ₁.restrictScalars C) (s i) = PR.map (ρ₂.restrictScalars C) (s j)) →
      ∃! s₀ : PR.obj A, ∀ i, PR.map (IsScalarTower.toAlgHom C A (B i)) s₀ = s i)

    (θ : ∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S],
      PR.obj S → (Omega K₀ π).obj S)
    (hnat : ∀ (S S' : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
      [CommRing S'] [Algebra C S'] [IsNoetherianRing S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 C S']
      (φ : S →ₐ[C] S') (x : PR.obj S),
      θ S' (PR.map φ x) = (Omega K₀ π).map (φ.restrictScalars 𝒪) (θ S x))

    (het : ∀ (S S₀ : Type) [CommRing S] [IsLocalRing S] [IsArtinianRing S] [IsAlgClosed (IsLocalRing.ResidueField S)]
      [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
      [CommRing S₀] [Nontrivial S₀] [Algebra C S₀] [IsNoetherianRing S₀] [Algebra 𝒪 S₀] [IsScalarTower 𝒪 C S₀]
      (p : S →ₐ[C] S₀), Function.Surjective p → (∀ s t : S, p s = 0 → p t = 0 → s * t = 0) →
      ∀ (x₀ : PR.obj S₀) (d : (Omega K₀ π).obj S),
        θ S₀ x₀ = (Omega K₀ π).map (p.restrictScalars 𝒪) d →
        ∃! x : PR.obj S, PR.map p x = x₀ ∧ θ S x = d)

    (hpts : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra C k] [Algebra 𝒪 k] [IsScalarTower 𝒪 C k],
      Function.Bijective (θ k))

    (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg : (g : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])

    (hrep : ∀ γ : Matrix.GeneralLinearGroup (Fin 2) K₀,
      ∃ (X : Scheme.{0}) (fX : X ⟶ Spec (CommRingCat.of C)) (_ : LocallyOfFiniteType fX)
        (e : ∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S],
          (Scheme.nilpPoints fX).obj S → PR.obj S),

        (∀ (S S' : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
            [CommRing S'] [Algebra C S'] [IsNoetherianRing S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 C S'] (φ : S →ₐ[C] S')
            (y : (Scheme.nilpPoints fX).obj S)
            (y' : (Scheme.nilpPoints fX).obj S'),
            y'.1 = Spec.map (CommRingCat.ofHom (φ : S →+* S')) ≫ y.1 → e S' y' = PR.map φ (e S y)) ∧

        (∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
            (y y' : (Scheme.nilpPoints fX).obj S), e S y = e S y' → y = y') ∧

        (∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S] (x : PR.obj S),
            (∃ y : (Scheme.nilpPoints fX).obj S, e S y = x) ↔
              DeligneDatum.InEdgeChart π (θ S x) (FullLattice.act γ (FullLattice.act g (stdFullLattice K₀)))
                (FullLattice.act γ (stdFullLattice K₀)))) :
    ∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S],
      Function.Bijective (θ S) := by
  classical

  have hnil : ∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S],
      IsNilpotent (algebraMap 𝒪 S π) := by
    intro S _ _ _ _
    rw [IsScalarTower.algebraMap_apply 𝒪 C S π]
    exact hC.map (algebraMap C S)

  have hlocal : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K₀)
      (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
      (d : (Omega K₀ π).obj S),
      DeligneDatum.InEdgeChart π d (FullLattice.act γ (FullLattice.act g (stdFullLattice K₀)))
        (FullLattice.act γ (stdFullLattice K₀)) →
      ∃! x : PR.obj S, θ S x = d :=
    p7_local π hπ q hq C hC PR θ hnat het hpts g hg hrep

  have hchart : ∀ (S S' : Type) [CommRing S] [Algebra 𝒪 S] [CommRing S'] [Algebra 𝒪 S'] (f : S →ₐ[𝒪] S')
      (d : (Omega K₀ π).obj S) (M' M : FullLattice 𝒪 K₀),
      DeligneDatum.InEdgeChart π d M' M → DeligneDatum.InEdgeChart π ((Omega K₀ π).map f d) M' M := by
    intro S S' _ _ _ _ f d M' M h 𝔮 h𝔮
    haveI := h𝔮
    exact (DeligneDatum.edgeNondegAt_map_iff_edgeNondegAt_comap π f d 𝔮 M' M).mpr (h _ inferInstance)

  have htow : ∀ (S T : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
      [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T] [Algebra S T] [IsScalarTower C S T]
      [IsScalarTower 𝒪 S T],
      (IsScalarTower.toAlgHom C S T).restrictScalars 𝒪 = IsScalarTower.toAlgHom 𝒪 S T :=
    fun S T _ _ _ _ _ _ _ _ _ _ _ => AlgHom.ext fun _ => rfl

  have hcover : ∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
      (d : (Omega K₀ π).obj S),
      ∃ (n : ℕ) (f : Fin n → S), Ideal.span (Set.range f) = ⊤ ∧
        ∀ i, ∃ γ : Matrix.GeneralLinearGroup (Fin 2) K₀, DeligneDatum.InEdgeChart π
          ((Omega K₀ π).map (IsScalarTower.toAlgHom 𝒪 S (Localization.Away (f i))) d)
          (FullLattice.act γ (FullLattice.act g (stdFullLattice K₀))) (FullLattice.act γ (stdFullLattice K₀)) := by
    intro S _ _ _ _ _ d
    obtain ⟨s, hs, hcov⟩ :=
      DeligneDatum.exists_cover_pullback_map_inEdgeChart_stdEdge_line_eq π hπ q hq g hg (hnil S) d
    refine ⟨s.card, fun i => ((s.equivFin.symm i) : S), ?_, ?_⟩
    · have hrange : Set.range (fun i : Fin s.card => ((s.equivFin.symm i) : S)) = ↑s := by
        ext x; constructor
        · rintro ⟨i, rfl⟩; exact (s.equivFin.symm i).2
        · intro hx; exact ⟨s.equivFin ⟨x, hx⟩, by simp⟩
      rw [hrange]; exact hs
    · intro i
      obtain ⟨h, x, hin, -, -⟩ := hcov _ (s.equivFin.symm i).2
      exact ⟨h, DeligneDatum.inEdgeChart_act_of_isPullback h (DeligneDatum.isPullback_pullback π _ h _) hin⟩

  have hinj : ∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S],
      Function.Injective (θ S) := by
    intro S _ _ _ _ _ x x' hxx
    obtain ⟨n, f, hf, hγ⟩ := hcover S (θ S x)
    refine (hsheaf S n f hf (fun i => Localization.Away (f i))
      (fun i => PR.map (IsScalarTower.toAlgHom C S (Localization.Away (f i))) x) ?_).unique (fun i => rfl) ?_
    · intro i j D _ _ _ _ _ ρ₁ ρ₂
      rw [← PR.map_comp, ← PR.map_comp]
      congr 1
      apply AlgHom.ext
      intro y
      simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, IsScalarTower.toAlgHom_apply, AlgHom.commutes]
    · intro i
      obtain ⟨γ, hγi⟩ := hγ i
      refine (hlocal γ (Localization.Away (f i)) _ hγi).unique ?_ ?_
      · rw [hnat, htow, ← hxx]
      · rw [hnat, htow]

  have hsurj : ∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
      (d : (Omega K₀ π).obj S), ∃ x : PR.obj S, θ S x = d := by
    intro S _ _ _ _ _ d
    obtain ⟨n, f, hf, hγ⟩ := hcover S d
    choose γ hγ using hγ
    have hsec : ∀ i, ∃ x : PR.obj (Localization.Away (f i)),
        θ _ x = (Omega K₀ π).map (IsScalarTower.toAlgHom 𝒪 S (Localization.Away (f i))) d :=
      fun i => (hlocal (γ i) (Localization.Away (f i)) _ (hγ i)).exists
    choose s hs using hsec
    obtain ⟨x, hx, -⟩ := hsheaf S n f hf (fun i => Localization.Away (f i)) s (by
      intro i j D _ _ _ _ _ ρ₁ ρ₂
      letI : Algebra 𝒪 D := ((algebraMap C D).comp (algebraMap 𝒪 C)).toAlgebra
      haveI : IsScalarTower 𝒪 C D := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      haveI : IsScalarTower 𝒪 S D := IsScalarTower.of_algebraMap_eq (fun y => by
        show algebraMap C D (algebraMap 𝒪 C y) = algebraMap S D (algebraMap 𝒪 S y)
        rw [IsScalarTower.algebraMap_apply 𝒪 C S y, ← IsScalarTower.algebraMap_apply C S D])
      haveI : IsNoetherianRing D := IsLocalization.isNoetherianRing (Submonoid.powers (f i * f j)) D inferInstance
      have hDd : ∀ (k : Fin n) (ρ : Localization.Away (f k) →ₐ[S] D),
          (Omega K₀ π).map ((ρ.restrictScalars C).restrictScalars 𝒪)
            ((Omega K₀ π).map (IsScalarTower.toAlgHom 𝒪 S (Localization.Away (f k))) d) =
          (Omega K₀ π).map (IsScalarTower.toAlgHom 𝒪 S D) d := by
        intro k ρ
        rw [← (Omega K₀ π).map_comp]
        congr 1
        apply AlgHom.ext
        intro y
        simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, IsScalarTower.toAlgHom_apply, AlgHom.commutes]
      have hin : DeligneDatum.InEdgeChart π ((Omega K₀ π).map (IsScalarTower.toAlgHom 𝒪 S D) d)
          (FullLattice.act (γ i) (FullLattice.act g (stdFullLattice K₀))) (FullLattice.act (γ i) (stdFullLattice K₀)) := by
        rw [← hDd i ρ₁]
        exact hchart _ _ _ _ _ _ (hγ i)
      refine (hlocal (γ i) D _ hin).unique ?_ ?_
      · rw [hnat, hs i, hDd i ρ₁]
      · rw [hnat, hs j, hDd j ρ₂])
    refine ⟨x, ?_⟩

    refine (CerednikDrinfeld.FormalOmega.Omega.existsUnique_glue_of_span_eq_top (K := K₀) π S f hf
      (fun i => Localization.Away (f i)) (fun i j => Localization.Away (f i * f j))
      (fun i j => ⟨IsLocalization.Away.awayToAwayRight (f i) (f j), IsLocalization.Away.awayToAwayRight_eq (f i) (f j)⟩)
      (fun i j => ⟨IsLocalization.Away.awayToAwayLeft (f j) (f i), IsLocalization.Away.awayToAwayLeft_eq (f j) (f i)⟩)
      (fun i => (Omega K₀ π).map (IsScalarTower.toAlgHom 𝒪 S (Localization.Away (f i))) d) ?_).unique ?_ (fun i => rfl)
    · intro i j
      rw [← (Omega K₀ π).map_comp, ← (Omega K₀ π).map_comp]
      congr 1
      apply AlgHom.ext
      intro y
      simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, IsScalarTower.toAlgHom_apply, AlgHom.commutes]
    · intro i
      rw [← htow S (Localization.Away (f i)), ← hnat, hx i, hs i, htow]
  exact fun S _ _ _ _ _ => ⟨hinj S, fun d => hsurj S d⟩

end
end S_CerednikDrinfeld_FormalOmega_Omega_bijective_of_algFunctor_of_forall_existsUnique_lift_of_forall_bijective_of_forall_represents_inEdgeChart
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_Omega_bijective_of_algFunctor_of_forall_existsUnique_lift_of_forall_bijective_of_forall_represents_inEdgeChart (solution)
