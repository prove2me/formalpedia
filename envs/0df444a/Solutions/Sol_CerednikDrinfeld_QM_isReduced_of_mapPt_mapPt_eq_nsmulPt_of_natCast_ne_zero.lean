-- Prove2me | solution 1 for CerednikDrinfeld.QM.isReduced_of_mapPt_mapPt_eq_nsmulPt_of_natCast_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/89685118-2e9c-5118-b9de-fae23d4dfc91

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_pullback_snd_of_isClosedImmersion_of_nsmul_eq_one
import Theorems.Thm_AlgebraicGeometry_isReduced_of_flat_of_formallyUnramified_of_isIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_isReduced_of_mapPt_mapPt_eq_nsmulPt_of_natCast_ne_zero

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM

universe u

noncomputable section

namespace P2mKerEtale

variable {k : Type u} [Field k]

theorem nsmulPt_eq_nsmul {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (n : ℕ) (P : SchemeHomOver t f) :
    nsmulPt L t n P = L.nsmul t n P := by
  induction n with
  | zero => rfl
  | succ n ih => rw [nsmulPt, ih, RelativeGroupLaw.nsmul_succ]

theorem mapPt_one {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)
    {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of k)} (L' : RelativeGroupLaw k f')
    (φ : A ⟶ A') (hφ : φ ≫ f' = f)
    (hφmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f),
      mapPt φ hφ (L.mul t P Q) = L'.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) :
    mapPt φ hφ (L.one t) = L'.one t := by
  letI := L'.pointGroup t
  have h := hφmul t (L.one t) (L.one t)
  rw [L.one_mul] at h
  have : mapPt φ hφ (L.one t) * mapPt φ hφ (L.one t) = mapPt φ hφ (L.one t) * 1 := by
    rw [mul_one]; exact h.symm
  exact mul_left_cancel this

theorem isReduced_of_isClosedImmersion_of_nsmul_eq_one
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f) (hc : L.IsCommutative)
    [LocallyOfFiniteType f] (n : ℕ) (hn : (n : k) ≠ 0)
    {K : Scheme.{u}} (i : K ⟶ A) [IsClosedImmersion i]
    (htors : L.nsmul (i ≫ f) n ⟨i, rfl⟩ = L.one (i ≫ f)) :
    IsReduced K := by
  have hu : IsUnit (n : k) := Ne.isUnit hn
  have h1 : FormallyUnramified (pullback.snd (i ≫ f) (𝟙 (Spec (CommRingCat.of k)))) :=
    RelativeGroupLaw.formallyUnramified_pullback_snd_of_isClosedImmersion_of_nsmul_eq_one
      (𝟙 (Spec (CommRingCat.of k))) L (fun t x y => hc t x y) n hu i htors

  have heq : i ≫ f = inv (pullback.fst (i ≫ f) (𝟙 (Spec (CommRingCat.of k)))) ≫
      pullback.snd (i ≫ f) (𝟙 (Spec (CommRingCat.of k))) := by
    rw [IsIso.eq_inv_comp, pullback.condition, Category.comp_id]
  haveI : FormallyUnramified (i ≫ f) := by
    rw [heq]
    exact MorphismProperty.comp_mem _ _ _ inferInstance h1
  exact AlgebraicGeometry.isReduced_of_flat_of_formallyUnramified_of_isIntegral (i ≫ f)

section Isog

variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)
  (hc : L.IsCommutative)
  {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of k)} (L' : RelativeGroupLaw k f')
  (φ : A ⟶ A') (hφ : φ ≫ f' = f)
  (hφmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f),
    mapPt φ hφ (L.mul t P Q) = L'.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
  (ψ : A' ⟶ A) (hψ : ψ ≫ f = f') (n : ℕ)
  (hψφ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t f),
    mapPt ψ hψ (mapPt φ hφ P) = nsmulPt L t n P)
  {K : Scheme.{u}} (i : K ⟶ A)
  (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t f),
    FactorsThrough i P → mapPt φ hφ P = L'.one t)

include hφmul hψφ hi in

theorem nsmul_tautological_eq_one : L.nsmul (i ≫ f) n ⟨i, rfl⟩ = L.one (i ≫ f) := by
  have hφi : mapPt φ hφ (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) = L'.one (i ≫ f) :=
    hi (i ≫ f) ⟨i, rfl⟩ ⟨𝟙 K, Category.id_comp i⟩
  have h1 := hψφ (i ≫ f) ⟨i, rfl⟩
  rw [hφi, ← mapPt_one L L' φ hφ hφmul (i ≫ f), hψφ, nsmulPt_eq_nsmul, nsmulPt_eq_nsmul,
    RelativeGroupLaw.nsmul_unit] at h1
  exact h1.symm

include hc hφmul hψφ hi in
theorem isReduced_ker [LocallyOfFiniteType f] (hn : (n : k) ≠ 0) [IsClosedImmersion i] : IsReduced K :=
  isReduced_of_isClosedImmersion_of_nsmul_eq_one L hc n hn i
    (nsmul_tautological_eq_one L L' φ hφ hφmul ψ hψ n hψφ i hi)

end Isog

end P2mKerEtale

end

open CerednikDrinfeld.QM in
theorem solution
    {k : Type u} [Field k]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)
    (hc : L.IsCommutative) [LocallyOfFiniteType f]
    {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of k)} (L' : RelativeGroupLaw k f')
    (φ : A ⟶ A') (hφ : φ ≫ f' = f)
    (hφmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f),
      mapPt φ hφ (L.mul t P Q) = L'.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (ψ : A' ⟶ A) (hψ : ψ ≫ f = f') (n : ℕ) (hn : (n : k) ≠ 0)
    (hψφ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t f),
      mapPt ψ hψ (mapPt φ hφ P) = nsmulPt L t n P)
    {K : Scheme.{u}} (i : K ⟶ A) [IsClosedImmersion i]
    (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t f),
      FactorsThrough i P → mapPt φ hφ P = L'.one t) :
    IsReduced K :=
  P2mKerEtale.isReduced_ker L hc L' φ hφ hφmul ψ hψ n hψφ i hi hn

end S_CerednikDrinfeld_QM_isReduced_of_mapPt_mapPt_eq_nsmulPt_of_natCast_ne_zero
end P2MW
export P2MW.S_CerednikDrinfeld_QM_isReduced_of_mapPt_mapPt_eq_nsmulPt_of_natCast_ne_zero (solution)
