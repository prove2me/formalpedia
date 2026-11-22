-- Prove2me | solution 1 for CGWH.isRightAdjoint_forgetToCG_and_hasLimits_and_hasColimits
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:27:55.328813+00:00
-- url     : https://prove2.me/submissions/f4603678-7306-4e22-96ce-6c10b1a3cb88

import Definitions.Def_CGWH_WeakHausdorff
import Theorems.Thm_CGWH_weakHausdorffification_universal

open CategoryTheory Topology TopologicalSpace

set_option autoImplicit false

universe u

namespace Sol_CGWH_isRightAdjoint_forgetToCG_and_hasLimits_and_hasColimits

open CGWH CategoryTheory.Limits

/-! ### The `k`-ification -/

/-- The `k`-ification of a topology is finer than the topology. -/
theorem compactlyGenerated_le (W : Type u) [t : TopologicalSpace W] :
    compactlyGenerated.{u} W ≤ t := by
  simp only [compactlyGenerated, ← continuous_iff_coinduced_le, continuous_sigma_iff,
    Sigma.forall]
  exact fun S f ↦ f.2

/-- A continuous map from a compact Hausdorff space (of the universe of `W`) to `W` is continuous
for the `k`-ified topology of `W`. -/
theorem continuous_kTop_of_compact {K W : Type u} [TopologicalSpace K] [CompactSpace K]
    [T2Space K] [t : TopologicalSpace W] {φ : K → W} (hφ : Continuous φ) :
    Continuous[inferInstance, compactlyGenerated.{u} W] φ := by
  let f : (Σ (i : (S : CompHaus.{u}) × C(S, W)), i.fst) → W := fun ⟨⟨_, i⟩, s⟩ ↦ i s
  suffices h : ∀ (i : (T : CompHaus.{u}) × C(T, W)),
      Continuous[inferInstance, compactlyGenerated.{u} W] (fun (a : i.fst) ↦ f ⟨i, a⟩) from
    h ⟨CompHaus.of K, ⟨φ, hφ⟩⟩
  rw [← @continuous_sigma_iff]
  apply continuous_coinduced_rng

/-- A continuous map from a compactly generated space to `W` is continuous for the `k`-ified
topology of `W`. -/
theorem continuous_kTop {T W : Type u} [TopologicalSpace T] [CompactlyGeneratedSpace T]
    [t : TopologicalSpace W] {φ : T → W} (hφ : Continuous φ) :
    Continuous[inferInstance, compactlyGenerated.{u} W] φ :=
  @continuous_from_compactlyGeneratedSpace T W _ (compactlyGenerated.{u} W) _ φ
    (fun _ _ _ _ _ hg => continuous_kTop_of_compact (hφ.comp hg))

/-- The `k`-ification of a topological space is compactly generated. -/
theorem compactlyGeneratedSpace_kTop (W : Type u) [t : TopologicalSpace W] :
    @CompactlyGeneratedSpace W (compactlyGenerated.{u} W) := by
  refine @uCompactlyGeneratedSpace_of_continuous_maps W (compactlyGenerated.{u} W)
    fun {Y} tY f h => ?_
  refine @continuous_from_compactlyGenerated W Y t tY f fun S g => ?_
  exact h S (@ContinuousMap.mk _ _ _ (compactlyGenerated.{u} W) g
    (continuous_kTop_of_compact (t := t) g.continuous))

/-! ### `CG` is coreflective in `Top` -/

/-- The `k`-ification `k(A)` of a topological space, as an object of `CG`. -/
def kObj (A : TopCat.{u}) : CompactlyGenerated.{u, u} :=
  @CompactlyGenerated.mk (@TopCat.of A (compactlyGenerated.{u} A))
    (compactlyGeneratedSpace_kTop A)

/-- The counit `k(A) → A`: the identity map. -/
def kCounit (A : TopCat.{u}) :
    CompactlyGenerated.compactlyGeneratedToTop.{u, u}.obj (kObj A) ⟶ A :=
  @TopCat.ofHom A A (compactlyGenerated.{u} A) _
    (@ContinuousMap.mk A A (compactlyGenerated.{u} A) _ id
      (continuous_id_iff_le.2 (compactlyGenerated_le A)))

/-- Universal property of the `k`-ification: for every topological space `A` the object
`(k(A), k(A) → A)` is terminal among the continuous maps from compactly generated spaces to `A`. -/
theorem hasTerminal_costructuredArrow (A : TopCat.{u}) :
    HasTerminal (CostructuredArrow CompactlyGenerated.compactlyGeneratedToTop.{u, u} A) := by
  have hne : ∀ Y : CostructuredArrow CompactlyGenerated.compactlyGeneratedToTop.{u, u} A,
      Nonempty (Y ⟶ CostructuredArrow.mk (kCounit A)) := by
    intro Y
    have hc : Continuous[inferInstance, compactlyGenerated.{u} A] (Y.hom : Y.left → A) :=
      continuous_kTop (T := Y.left) (Y.hom.hom.continuous)
    let g : Y.left ⟶ kObj A :=
      InducedCategory.homMk (@TopCat.ofHom Y.left A _ (compactlyGenerated.{u} A)
        (@ContinuousMap.mk Y.left A _ (compactlyGenerated.{u} A) Y.hom hc))
    exact ⟨CostructuredArrow.homMk g (by ext x; rfl)⟩
  have hss : ∀ Y : CostructuredArrow CompactlyGenerated.compactlyGeneratedToTop.{u, u} A,
      Subsingleton (Y ⟶ CostructuredArrow.mk (kCounit A)) := by
    intro Y
    refine ⟨fun a b => ?_⟩
    have ha := CostructuredArrow.w a
    have hb := CostructuredArrow.w b
    ext x
    have h1 := congrArg (fun φ => (ConcreteCategory.hom φ) x) ha
    have h2 := congrArg (fun φ => (ConcreteCategory.hom φ) x) hb
    exact h1.trans h2.symm
  exact hasTerminal_of_unique (CostructuredArrow.mk (kCounit A))

/-- The inclusion `CG ⥤ Top` has a right adjoint (the `k`-ification). -/
theorem isLeftAdjoint_compactlyGeneratedToTop :
    CompactlyGenerated.compactlyGeneratedToTop.{u, u}.IsLeftAdjoint := by
  have := hasTerminal_costructuredArrow.{u}
  exact isLeftAdjoint_of_costructuredArrowTerminals _

/-- `CG` has all small limits, as a coreflective full subcategory of `Top`. -/
theorem hasLimits_compactlyGenerated : HasLimits CompactlyGenerated.{u, u} := by
  have := isLeftAdjoint_compactlyGeneratedToTop.{u}
  have : Coreflective CompactlyGenerated.compactlyGeneratedToTop.{u, u} :=
    { R := CompactlyGenerated.compactlyGeneratedToTop.{u, u}.rightAdjoint
      adj := Adjunction.ofIsLeftAdjoint _ }
  exact hasLimits_of_coreflective CompactlyGenerated.compactlyGeneratedToTop.{u, u}

/-- `CG` has all small colimits, as a coreflective full subcategory of `Top`. -/
theorem hasColimits_compactlyGenerated : HasColimits CompactlyGenerated.{u, u} := by
  have := isLeftAdjoint_compactlyGeneratedToTop.{u}
  have : Coreflective CompactlyGenerated.compactlyGeneratedToTop.{u, u} :=
    { R := CompactlyGenerated.compactlyGeneratedToTop.{u, u}.rightAdjoint
      adj := Adjunction.ofIsLeftAdjoint _ }
  exact hasColimits_of_coreflective CompactlyGenerated.compactlyGeneratedToTop.{u, u}

/-! ### `CGWH` is reflective in `CG` -/

/-- For every compactly generated space `X` the object `(h(X), q_X : X → h(X))` is initial among
the continuous maps from `X` to compactly generated weakly Hausdorff spaces: this is the universal
property of the weak Hausdorffification. -/
theorem hasInitial_structuredArrow (X : CompactlyGenerated.{u, u}) :
    HasInitial (StructuredArrow X forgetToCG.{u}) := by
  obtain ⟨hCG, hWH, huniv⟩ := CGWH.weakHausdorffification_universal X
  let hX : CGWHCat.{u} :=
    ⟨@CompactlyGenerated.mk (TopCat.of (WeakHausdorffification X)) hCG, hWH⟩
  have hq : Continuous (WeakHausdorffification.mk : X → WeakHausdorffification X) :=
    continuous_quotient_mk'
  let q : X ⟶ forgetToCG.{u}.obj hX :=
    InducedCategory.homMk (TopCat.ofHom (X := X) (Y := WeakHausdorffification X)
      ⟨WeakHausdorffification.mk, hq⟩)
  have hne : ∀ Y : StructuredArrow X forgetToCG.{u},
      Nonempty (StructuredArrow.mk q ⟶ Y) := by
    intro Y
    have : WeaklyHausdorffSpace Y.right.obj := Y.right.property
    obtain ⟨g, hg, -⟩ := huniv Y.right.obj (ConcreteCategory.hom Y.hom)
    let g' : hX ⟶ Y.right :=
      ObjectProperty.homMk (InducedCategory.homMk
        (TopCat.ofHom (X := WeakHausdorffification X) (Y := Y.right.obj) g))
    refine ⟨StructuredArrow.homMk g' ?_⟩
    ext x
    exact hg x
  have hss : ∀ Y : StructuredArrow X forgetToCG.{u},
      Subsingleton (StructuredArrow.mk q ⟶ Y) := by
    intro Y
    have : WeaklyHausdorffSpace Y.right.obj := Y.right.property
    refine ⟨fun a b => ?_⟩
    have ha := StructuredArrow.w a
    have hb := StructuredArrow.w b
    obtain ⟨g, -, huniq⟩ := huniv Y.right.obj (ConcreteCategory.hom Y.hom)
    have h1 : ConcreteCategory.hom a.right.hom = g := huniq _ fun x =>
      congrArg (fun φ => (ConcreteCategory.hom φ) x) ha
    have h2 : ConcreteCategory.hom b.right.hom = g := huniq _ fun x =>
      congrArg (fun φ => (ConcreteCategory.hom φ) x) hb
    ext x
    exact congrArg (fun φ : C(WeakHausdorffification X, Y.right.obj) => φ x) (h1.trans h2.symm)
  exact hasInitial_of_unique (StructuredArrow.mk q)

/-- The inclusion `CGWH ⥤ CG` has a left adjoint. -/
theorem isRightAdjoint_forgetToCG : (forgetToCG.{u}).IsRightAdjoint := by
  have := hasInitial_structuredArrow.{u}
  exact isRightAdjointOfStructuredArrowInitials _

end Sol_CGWH_isRightAdjoint_forgetToCG_and_hasLimits_and_hasColimits

open CGWH

theorem solution :
    (forgetToCG.{u}).IsRightAdjoint ∧ Limits.HasLimits CGWHCat.{u} ∧
      Limits.HasColimits CGWHCat.{u} := by
  have hadj := Sol_CGWH_isRightAdjoint_forgetToCG_and_hasLimits_and_hasColimits.isRightAdjoint_forgetToCG.{u}
  have hlim := Sol_CGWH_isRightAdjoint_forgetToCG_and_hasLimits_and_hasColimits.hasLimits_compactlyGenerated.{u}
  have hcolim := Sol_CGWH_isRightAdjoint_forgetToCG_and_hasLimits_and_hasColimits.hasColimits_compactlyGenerated.{u}
  have : Reflective forgetToCG.{u} :=
    { L := forgetToCG.{u}.leftAdjoint
      adj := Adjunction.ofIsRightAdjoint _ }
  exact ⟨hadj, hasLimits_of_reflective forgetToCG.{u}, hasColimits_of_reflective forgetToCG.{u}⟩
