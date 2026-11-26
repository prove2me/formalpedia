-- Prove2me | solution 1 for CategoryTheory.Functor.rightDerived_linear_of_linear
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-26T21:28:38.730156+00:00
-- url     : https://prove2.me/submissions/7c4bfd49-006a-4fe3-aaba-7722bea63fe6

import Mathlib

set_option autoImplicit false

universe w v v' u u'

open CategoryTheory Limits

namespace RamanujanPetersson.EtLin

theorem homologyMap_smul' {R : Type w} [Semiring R] {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
    {ι : Type*} {c : ComplexShape ι} {K L : HomologicalComplex C c} (r : R) (φ : K ⟶ L) (i : ι) [K.HasHomology i]
    [L.HasHomology i] : HomologicalComplex.homologyMap (r • φ) i = r • HomologicalComplex.homologyMap φ i :=
  ShortComplex.homologyMap_smul ((HomologicalComplex.shortComplexFunctor C c i).map φ) r

instance homologyFunctor_linear' {R : Type w} [Semiring R] {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear R C] {ι : Type*} {c : ComplexShape ι} [CategoryWithHomology C] (i : ι) :
    (HomologicalComplex.homologyFunctor C c i).Linear R where
  map_smul f r := homologyMap_smul' r f i

theorem conj_smul_id {R : Type w} [Semiring R] {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear R D]
    {X Y : D} (e : X ≅ Y) (r : R) : e.hom ≫ (r • 𝟙 Y) ≫ e.inv = r • 𝟙 X := by
  simp

end RamanujanPetersson.EtLin

theorem solution
    {R : Type w} [Semiring R]
    {C : Type u} [Category.{v} C] [Abelian C] [CategoryTheory.Linear R C] [HasInjectiveResolutions C]
    {D : Type u'} [Category.{v'} D] [Abelian D] [CategoryTheory.Linear R D]
    (F : C ⥤ D) [F.Additive] [F.Linear R] (n : ℕ) :
    (F.rightDerived n).Linear R := by
  rw [Functor.linear_iff]
  intro X r
  have w : (injectiveResolution X).ι ≫ (r • 𝟙 (injectiveResolution X).cocomplex) =
      (CochainComplex.single₀ C).map (r • 𝟙 X) ≫ (injectiveResolution X).ι := by
    apply HomologicalComplex.from_single_hom_ext
    simp only [HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero, HomologicalComplex.smul_f_apply,
      Linear.comp_smul, Category.comp_id]
    erw [Linear.smul_comp, Category.id_comp]
  rw [F.rightDerived_map_eq n (r • 𝟙 X) _ w, Functor.map_smul, CategoryTheory.Functor.map_id]
  exact RamanujanPetersson.EtLin.conj_smul_id _ r
