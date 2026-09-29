-- Prove2me | solution 1 for CategoryTheory.Functor.exists_overTotal_chart_relative_isOpenImmersion_of_representableBy_over_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/95b0652a-1609-57ce-b683-ba7bb0dcb36f

import Mathlib
import Definitions.Def_CategoryTheory_OverTotalPresheaf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CategoryTheory_Functor_exists_overTotal_chart_relative_isOpenImmersion_of_representableBy_over_map

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace TotRestrict

variable {S U : Scheme.{u}} (j : U ⟶ S) [IsOpenImmersion j]
  (G : (Over S)ᵒᵖ ⥤ Type (u + 1)) {Y : Scheme.{u}} (p : Y ⟶ U)
  (e : ((Over.map j).op ⋙ G).RepresentableBy (Over.mk p))

noncomputable def chart : uliftYoneda.{u + 1}.obj Y ⟶ G.overTotal :=
  uliftYonedaEquiv.symm ⟨p ≫ j, e.homEquiv (𝟙 (Over.mk p))⟩

omit [IsOpenImmersion j] in
theorem uliftYonedaEquiv_chart :
    uliftYonedaEquiv (chart j G p e) = ⟨p ≫ j, e.homEquiv (𝟙 (Over.mk p))⟩ := by
  rw [chart, Equiv.apply_symm_apply]

omit [IsOpenImmersion j] in

theorem chart_apply {T : Scheme.{u}} (y : T ⟶ Y) :
    uliftYonedaEquiv (uliftYoneda.{u + 1}.map y ≫ chart j G p e) =
      ⟨(y ≫ p) ≫ j, e.homEquiv (Over.homMk y rfl : Over.mk (y ≫ p) ⟶ Over.mk p)⟩ := by
  have hn := uliftYonedaEquiv_naturality (chart j G p e) y.op
  simp only [Quiver.Hom.unop_op] at hn
  rw [← hn, uliftYonedaEquiv_chart]
  refine Functor.OverTotal.ext' (Category.assoc y p j).symm ?_
  rw [e.homEquiv_eq (Over.homMk y rfl : Over.mk (y ≫ p) ⟶ Over.mk p)]
  exact (Functor.map_op_map_op_apply _ _ _).trans (Functor.map_op_apply_eq_of_left_eq _ _ (by simp) _)

theorem chart_apply_fst {T : Scheme.{u}} (y : T ⟶ Y) :
    (uliftYonedaEquiv (uliftYoneda.{u + 1}.map y ≫ chart j G p e)).1 = (y ≫ p) ≫ j := by
  rw [chart_apply]

theorem toFibre_chart_apply {T : Scheme.{u}} (y : T ⟶ Y)
    (h : (uliftYonedaEquiv (uliftYoneda.{u + 1}.map y ≫ chart j G p e)).1 = (Over.mk ((y ≫ p) ≫ j)).hom) :
    Functor.OverTotal.toFibre (Over.mk ((y ≫ p) ≫ j)) (uliftYonedaEquiv (uliftYoneda.{u + 1}.map y ≫ chart j G p e)) h =
      e.homEquiv (Over.homMk y rfl : Over.mk (y ≫ p) ⟶ Over.mk p) := by
  rw [Functor.OverTotal.toFibre_congr _ (chart_apply j G p e y) h rfl]
  exact Functor.map_op_apply_eq_self _ (by simp) _

theorem eq_of_chart_eq {T : Scheme.{u}} (y y' : T ⟶ Y)
    (h : uliftYonedaEquiv (uliftYoneda.{u + 1}.map y ≫ chart j G p e) =
      uliftYonedaEquiv (uliftYoneda.{u + 1}.map y' ≫ chart j G p e)) : y = y' := by
  have h1 : (y ≫ p) ≫ j = (y' ≫ p) ≫ j := by
    have := congrArg Sigma.fst h
    rwa [chart_apply_fst, chart_apply_fst] at this
  have hp : y ≫ p = y' ≫ p := by rwa [cancel_mono] at h1
  have hy : Functor.OverTotal.toFibre (Over.mk ((y ≫ p) ≫ j))
      (uliftYonedaEquiv (uliftYoneda.{u + 1}.map y ≫ chart j G p e)) (chart_apply_fst j G p e y) =
      Functor.OverTotal.toFibre (Over.mk ((y ≫ p) ≫ j))
      (uliftYonedaEquiv (uliftYoneda.{u + 1}.map y' ≫ chart j G p e)) ((chart_apply_fst j G p e y').trans h1.symm) :=
    Functor.OverTotal.toFibre_congr _ h _ _
  rw [toFibre_chart_apply] at hy

  rw [Functor.OverTotal.toFibre_congr _ (chart_apply j G p e y') _ (h1.symm)] at hy
  have key : (Over.homMk y rfl : Over.mk (y ≫ p) ⟶ Over.mk p) =
      (Over.homMk (𝟙 T) (show 𝟙 T ≫ (y' ≫ p) = y ≫ p by rw [Category.id_comp, hp]) : Over.mk (y ≫ p) ⟶ Over.mk (y' ≫ p)) ≫
        (Over.homMk y' rfl : Over.mk (y' ≫ p) ⟶ Over.mk p) := by
    apply e.homEquiv.injective
    rw [hy, e.homEquiv_comp]
    exact Functor.map_op_apply_eq_of_left_eq _ _ rfl _
  have := congrArg (fun k => k.left) key
  simpa using this

omit [IsOpenImmersion j] in

theorem chart_apply_over {X : Over U} (k : X ⟶ Over.mk p) :
    uliftYonedaEquiv (uliftYoneda.{u + 1}.map k.left ≫ chart j G p e) =
      Functor.OverTotal.ofFibre ((Over.map j).obj X) (e.homEquiv k) := by
  have hn : G.overTotal.map k.left.op (uliftYonedaEquiv (chart j G p e)) =
      uliftYonedaEquiv (uliftYoneda.{u + 1}.map k.left ≫ chart j G p e) := uliftYonedaEquiv_naturality _ _
  rw [← hn, uliftYonedaEquiv_chart, e.homEquiv_eq k]
  refine Functor.OverTotal.ext' ?_ ?_
  · show k.left ≫ p ≫ j = X.hom ≫ j
    rw [← Category.assoc]
    congr 1
    simpa using Over.w k
  ·
    refine (Functor.map_op_map_op_apply _ _ _).trans ?_
    refine Eq.trans ?_ (Functor.map_op_map_op_apply _ _ _).symm
    exact Functor.map_op_apply_eq_of_left_eq _ _ (by simp) _

omit [IsOpenImmersion j] in

theorem app_eq {X : Scheme.{u}} {F : Scheme.{u}ᵒᵖ ⥤ Type (u + 1)} (τ : uliftYoneda.{u + 1}.obj X ⟶ F)
    (Z : Scheme.{u}ᵒᵖ) (a : (uliftYoneda.{u + 1}.obj X).obj Z) :
    τ.app Z a = uliftYonedaEquiv (uliftYoneda.{u + 1}.map a.down ≫ τ) := by
  obtain ⟨T⟩ := Z
  rw [uliftYonedaEquiv_apply]
  show τ.app (op T) a = τ.app (op T) ((uliftYoneda.{u + 1}.map a.down).app (op T) ⟨𝟙 T⟩)
  simp [uliftYoneda_map_app]

theorem exists_fac {T : Scheme.{u}} (x : uliftYoneda.{u + 1}.obj T ⟶ G.overTotal)
    (hx : Set.range ((uliftYonedaEquiv x).1).base ⊆ Set.range j.base) :
    ∃ ψ : T ⟶ Y, uliftYoneda.{u + 1}.map ψ ≫ chart j G p e = x := by
  set t := (uliftYonedaEquiv x).1 with ht
  let t' : T ⟶ U := IsOpenImmersion.lift j t hx
  have ht' : t' ≫ j = t := IsOpenImmersion.lift_fac j t hx
  let ξ' : G.obj (op ((Over.map j).obj (Over.mk t'))) :=
    Functor.OverTotal.toFibre ((Over.map j).obj (Over.mk t')) (uliftYonedaEquiv x) (by exact ht'.symm)
  let ψbar : Over.mk t' ⟶ Over.mk p := e.homEquiv.symm ξ'
  refine ⟨ψbar.left, ?_⟩
  apply uliftYonedaEquiv.injective
  refine (chart_apply_over j G p e ψbar).trans ?_
  show Functor.OverTotal.ofFibre ((Over.map j).obj (Over.mk t')) (e.homEquiv (e.homEquiv.symm ξ')) = uliftYonedaEquiv x
  rw [Equiv.apply_symm_apply]
  exact Functor.OverTotal.ofFibre_toFibre _ _ _

theorem isPullback {T : Scheme.{u}} (g : uliftYoneda.{u + 1}.obj T ⟶ G.overTotal) :
    ∃ (ψ : ((((uliftYonedaEquiv g).1) ⁻¹ᵁ (Scheme.Hom.opensRange j) : T.Opens) : Scheme.{u}) ⟶ Y),
      IsPullback (uliftYoneda.{u + 1}.map ψ)
        (uliftYoneda.{u + 1}.map (((uliftYonedaEquiv g).1) ⁻¹ᵁ (Scheme.Hom.opensRange j)).ι) (chart j G p e) g := by
  set t := (uliftYonedaEquiv g).1 with ht
  set V : T.Opens := t ⁻¹ᵁ (Scheme.Hom.opensRange j) with hV

  have hrange : Set.range ((uliftYonedaEquiv (uliftYoneda.{u + 1}.map V.ι ≫ g)).1).base ⊆ Set.range j.base := by
    have hn : G.overTotal.map V.ι.op (uliftYonedaEquiv g) = uliftYonedaEquiv (uliftYoneda.{u + 1}.map V.ι ≫ g) :=
      uliftYonedaEquiv_naturality _ _
    rw [← hn]
    rintro _ ⟨v, rfl⟩
    show t.base (V.ι.base v) ∈ Set.range j.base
    rw [← Scheme.Hom.coe_opensRange]
    exact v.2
  obtain ⟨ψ, hψ⟩ := exists_fac j G p e (uliftYoneda.{u + 1}.map V.ι ≫ g) hrange
  refine ⟨ψ, IsPullback.of_isLimit' ⟨hψ⟩ (PullbackCone.IsLimit.mk hψ ?lift ?fac1 ?fac2 ?uniq)⟩

  · intro s
    have hmem : ∀ (Z : Scheme.{u}ᵒᵖ) (q : s.pt.obj Z),
        Set.range ((s.snd.app Z q).down).base ⊆ Set.range V.ι.base := by
      intro Z q
      have hc := congrFun (congrArg (fun τ => τ.app Z) s.condition) q

      have h1 : ((s.fst.app Z q).down ≫ p) ≫ j = (s.snd.app Z q).down ≫ t := by
        have := congrArg Sigma.fst hc
        simp only [FunctorToTypes.comp] at this
        have hn : G.overTotal.map ((s.snd.app Z q).down).op (uliftYonedaEquiv g) =
            uliftYonedaEquiv (uliftYoneda.{u + 1}.map (s.snd.app Z q).down ≫ g) := uliftYonedaEquiv_naturality _ _
        rw [app_eq, app_eq, chart_apply_fst, ← hn] at this
        exact this
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      show t.base (((s.snd.app Z q).down).base z) ∈ (Scheme.Hom.opensRange j : Set S)
      rw [Scheme.Hom.coe_opensRange]
      refine ⟨p.base (((s.fst.app Z q).down).base z), ?_⟩
      have := congrArg (fun φ => φ.base z) h1
      exact this
    exact
      { app := fun Z => TypeCat.ofHom (fun q => ⟨IsOpenImmersion.lift V.ι (s.snd.app Z q).down (hmem Z q)⟩)
        naturality := by
          intro Z Z' f
          ext q
          apply ULift.ext
          show IsOpenImmersion.lift V.ι (s.snd.app Z' (s.pt.map f q)).down (hmem Z' _) =
            f.unop ≫ IsOpenImmersion.lift V.ι (s.snd.app Z q).down (hmem Z q)
          symm
          apply IsOpenImmersion.lift_uniq
          rw [Category.assoc, IsOpenImmersion.lift_fac]
          have hnat := NatTrans.naturality_apply s.snd f q

          rw [hnat]
          rfl }
  · intro s
    ext Z q
    apply ULift.ext
    show (IsOpenImmersion.lift V.ι (s.snd.app Z q).down _) ≫ ψ = (s.fst.app Z q).down
    apply eq_of_chart_eq j G p e
    rw [uliftYoneda.{u + 1}.map_comp, Category.assoc, hψ, ← Category.assoc, ← uliftYoneda.{u + 1}.map_comp,
      IsOpenImmersion.lift_fac]
    have hc := congrFun (congrArg (fun τ => τ.app Z) s.condition) q
    simp only [FunctorToTypes.comp] at hc
    rw [app_eq, app_eq] at hc
    exact hc.symm
  · intro s
    ext Z q
    apply ULift.ext
    show (IsOpenImmersion.lift V.ι (s.snd.app Z q).down _) ≫ V.ι = (s.snd.app Z q).down
    exact IsOpenImmersion.lift_fac _ _ _
  · intro s m hm1 hm2
    ext Z q
    apply ULift.ext
    apply IsOpenImmersion.lift_uniq
    have := congrFun (congrArg (fun τ => τ.app Z) hm2) q
    simp only [FunctorToTypes.comp] at this
    rw [← this]
    rfl

theorem main :
    ∃ φ : uliftYoneda.{u + 1}.obj Y ⟶ G.overTotal,
      (∀ {T : Scheme.{u}} (y : T ⟶ Y),
        uliftYonedaEquiv (uliftYoneda.{u + 1}.map y ≫ φ) =
          ⟨(y ≫ p) ≫ j, e.homEquiv (Over.homMk y rfl : Over.mk (y ≫ p) ⟶ Over.mk p)⟩) ∧
      MorphismProperty.relative uliftYoneda.{u + 1} @IsOpenImmersion φ ∧
      ∀ {T : Scheme.{u}} (x : uliftYoneda.{u + 1}.obj T ⟶ G.overTotal),
        Set.range ((uliftYonedaEquiv x).1).base ⊆ Set.range j.base →
        ∃ ψ : T ⟶ Y, uliftYoneda.{u + 1}.map ψ ≫ φ = x := by
  refine ⟨chart j G p e, fun y => chart_apply j G p e y, ?_, fun x hx => exists_fac j G p e x hx⟩
  apply MorphismProperty.relative.of_exists
  intro T g
  obtain ⟨ψ, hpb⟩ := isPullback j G p e g
  exact ⟨_, _, _, hpb, inferInstance⟩

end TotRestrict

theorem solution
    {S U : Scheme.{u}} (j : U ⟶ S) [IsOpenImmersion j]
    (G : (Over S)ᵒᵖ ⥤ Type (u + 1))
    {Y : Scheme.{u}} (p : Y ⟶ U) (e : ((Over.map j).op ⋙ G).RepresentableBy (Over.mk p)) :
    ∃ φ : uliftYoneda.{u + 1}.obj Y ⟶ G.overTotal,
      (∀ {T : Scheme.{u}} (y : T ⟶ Y),
        uliftYonedaEquiv (uliftYoneda.{u + 1}.map y ≫ φ) =
          ⟨(y ≫ p) ≫ j, e.homEquiv (Over.homMk y rfl : Over.mk (y ≫ p) ⟶ Over.mk p)⟩) ∧
      MorphismProperty.relative uliftYoneda.{u + 1} @IsOpenImmersion φ ∧
      ∀ {T : Scheme.{u}} (x : uliftYoneda.{u + 1}.obj T ⟶ G.overTotal),
        Set.range ((uliftYonedaEquiv x).1).base ⊆ Set.range j.base →
        ∃ ψ : T ⟶ Y, uliftYoneda.{u + 1}.map ψ ≫ φ = x := by
  exact TotRestrict.main j G p e

end S_CategoryTheory_Functor_exists_overTotal_chart_relative_isOpenImmersion_of_representableBy_over_map
end P2MW
export P2MW.S_CategoryTheory_Functor_exists_overTotal_chart_relative_isOpenImmersion_of_representableBy_over_map (solution)
