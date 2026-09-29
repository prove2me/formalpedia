-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_isClosedImmersion_factorsThrough_iff_nsmulPt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/af14d6b1-2753-5deb-9b26-41c8a2a4aca1

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_isClosedImmersion_factorsThrough_iff_nsmulPt

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
p2m_open "CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_isClosedImmersion_factorsThrough_iff_nsmulPt.CerednikDrinfeld CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_isClosedImmersion_factorsThrough_iff_nsmulPt.CerednikDrinfeld.QM NeronModelInfra"

open CategoryTheory.Limits GoodReductionJacobian

universe u

namespace CerednikDrinfeld
namespace QM
p2m_export "CerednikDrinfeld.QM" "FakeEllipticCurve.WithExtraLevel FactorsThrough nsmulPt FakeEllipticCurve"
namespace CombineSubgroupBody
p2m_open "CerednikDrinfeld.QM CerednikDrinfeld"

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem nsmulPt_eq_nsmul (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (n : ℕ) (P : SchemeHomOver t f) : nsmulPt L t n P = L.nsmul t n P := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [RelativeGroupLaw.nsmul_succ, ← ih]
    rfl

theorem comp_schemeNsmul (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (P : SchemeHomOver t f) (n : ℕ) : P.1 ≫ L.schemeNsmul n = (nsmulPt L t n P).1 := by
  have hnat := congrArg Subtype.val (L.nsmul_natural f t P.1 P.2 n RelativeGroupLaw.idPoint)
  rw [schemeHomOverComp_coe] at hnat
  have hP : schemeHomOverComp P.1 P.2 (RelativeGroupLaw.idPoint (f := f)) = P :=
    Subtype.ext (by rw [schemeHomOverComp_coe]; exact Category.comp_id _)
  rw [hP, ← nsmulPt_eq_nsmul L t n P] at hnat
  exact hnat

end CerednikDrinfeld.QM.CombineSubgroupBody

open CategoryTheory.Limits GoodReductionJacobian CerednikDrinfeld.QM.CombineSubgroupBody in
theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N ℓ : ℕ)
    (S : Type) [CommRing S] (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) :
    ∃ (C' : Scheme.{0}) (lev' : C' ⟶ u.1.A), IsClosedImmersion lev' ∧
      ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
        FactorsThrough lev' P ↔
          FactorsThrough u.1.lev (nsmulPt u.1.L t ℓ P) ∧ FactorsThrough u.2.levK (nsmulPt u.1.L t N P) := by

  let L := u.1.L
  let j₁ : pullback u.1.lev (L.schemeNsmul ℓ) ⟶ u.1.A := pullback.snd u.1.lev (L.schemeNsmul ℓ)
  let j₂ : pullback u.2.levK (L.schemeNsmul N) ⟶ u.1.A := pullback.snd u.2.levK (L.schemeNsmul N)
  haveI : IsClosedImmersion u.1.lev := u.1.lev_closed
  haveI : IsClosedImmersion u.2.levK := u.2.levK_closed
  haveI hj₁ : IsClosedImmersion j₁ := inferInstance
  haveI hj₂ : IsClosedImmersion j₂ := inferInstance
  refine ⟨pullback j₁ j₂, pullback.fst j₁ j₂ ≫ j₁, inferInstance, ?_⟩
  intro T t P
  constructor
  · rintro ⟨P₀, hP₀⟩
    refine ⟨⟨P₀ ≫ pullback.fst j₁ j₂ ≫ pullback.fst u.1.lev (L.schemeNsmul ℓ), ?_⟩,
      ⟨P₀ ≫ pullback.snd j₁ j₂ ≫ pullback.fst u.2.levK (L.schemeNsmul N), ?_⟩⟩
    · rw [← comp_schemeNsmul, ← hP₀]
      simp only [Category.assoc]
      rw [pullback.condition]
    · rw [← comp_schemeNsmul, ← hP₀]
      simp only [Category.assoc]
      rw [pullback.condition, ← pullback.condition_assoc]
  · rintro ⟨⟨c₀, hc₀⟩, ⟨k₀, hk₀⟩⟩
    rw [← comp_schemeNsmul] at hc₀ hk₀
    let a₁ : T ⟶ pullback u.1.lev (L.schemeNsmul ℓ) := pullback.lift c₀ P.1 hc₀
    let a₂ : T ⟶ pullback u.2.levK (L.schemeNsmul N) := pullback.lift k₀ P.1 hk₀
    have ha₁ : a₁ ≫ j₁ = P.1 := pullback.lift_snd _ _ _
    have ha₂ : a₂ ≫ j₂ = P.1 := pullback.lift_snd _ _ _
    refine ⟨pullback.lift a₁ a₂ (by rw [ha₁, ha₂]), ?_⟩
    rw [← Category.assoc, pullback.lift_fst, ha₁]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_isClosedImmersion_factorsThrough_iff_nsmulPt
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_isClosedImmersion_factorsThrough_iff_nsmulPt (solution)
