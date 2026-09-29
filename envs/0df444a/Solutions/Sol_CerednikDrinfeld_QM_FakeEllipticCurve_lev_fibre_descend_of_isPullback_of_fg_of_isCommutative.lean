-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.lev_fibre_descend_of_isPullback_of_fg_of_isCommutative
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/89b110fe-0676-5b2f-bd0e-8d2701da1611

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_factorsThrough_nsmulPt_eq_one_eq_sq_of_isPullback_of_fg_of_isCommutative
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_zmod_prod_equiv_of_natCard_nsmul_eq_one_eq_sq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_lev_fibre_descend_of_isPullback_of_fg_of_isCommutative
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

theorem G2Asm.nsmul_eq_nsmulPt {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t f) :
    L.nsmul t n P = nsmulPt L t n P := by
  induction n with
  | zero => rw [RelativeGroupLaw.nsmul_zero]; rfl
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, ih]; rfl

theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N : ℕ)
    (L : Type) [CommRing L] (E : FakeEllipticCurve Λ N L)
    (R : Subalgebra ℤ L) (hR : R.FG)
    (A₀ : Scheme.{0}) (f₀ : A₀ ⟶ Spec (CommRingCat.of ↥R)) (L₀ : RelativeGroupLaw ↥R f₀)
    (hcomm₀ : L₀.IsCommutative) (hbundle₀ : AbelianSchemePropertyBundle ↥R f₀)
    (C₀ : Scheme.{0}) (lev₀ : C₀ ⟶ A₀) (hlev_closed₀ : IsClosedImmersion lev₀)
    (hlev_sub₀ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥R)) (P Q : SchemeHomOver t f₀),
      FactorsThrough lev₀ P → FactorsThrough lev₀ Q → FactorsThrough lev₀ (L₀.mul t P Q) ∧ FactorsThrough lev₀ (L₀.inv t P))
    (hlev_one₀ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥R)), FactorsThrough lev₀ (L₀.one t))
    (hlev_torsion₀ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥R)) (P : SchemeHomOver t f₀),
      FactorsThrough lev₀ P → nsmulPt L₀ t N P = L₀.one t)
    (hlev_finite₀ : IsFinite (lev₀ ≫ f₀)) (hlev_flat₀ : Flat (lev₀ ≫ f₀)) (hlev_fp₀ : LocallyOfFinitePresentation (lev₀ ≫ f₀))
    (hlev_rank₀ : ∀ s : ↥(Spec (CommRingCat.of ↥R)), (lev₀ ≫ f₀).finrank s = N ^ 2)
    (g : E.A ⟶ A₀) (hg : CategoryTheory.IsPullback g E.f f₀ (Spec.map (CommRingCat.ofHom R.val.toRingHom)))
    (hmul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of L)) (P Q : SchemeHomOver t' E.f),
      (E.L.mul t' P Q).1 ≫ g =
        (L₀.mul (t' ≫ Spec.map (CommRingCat.ofHom R.val.toRingHom))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    (gC : E.C ⟶ C₀) (hgC : CategoryTheory.IsPullback gC E.lev lev₀ g) :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : ↥R →+* k), (N : k) ≠ 0 →
      ∃ e : ZMod N × ZMod N ≃ {P : SchemeHomOver (geomPoint k sk) f₀ // FactorsThrough lev₀ P},
        ∀ x y : ZMod N × ZMod N, (e (x + y) : SchemeHomOver (geomPoint k sk) f₀) = L₀.mul (geomPoint k sk) (e x) (e y) := by
  intro k _ _ sk hNk
  have hcount := CerednikDrinfeld.QM.FakeEllipticCurve.natCard_factorsThrough_nsmulPt_eq_one_eq_sq_of_isPullback_of_fg_of_isCommutative
    Λ N L E R hR A₀ f₀ L₀ hcomm₀ hbundle₀ C₀ lev₀ hlev_closed₀ hlev_sub₀ hlev_one₀ hlev_torsion₀ hlev_finite₀ hlev_flat₀ hlev_fp₀
    hlev_rank₀ g hg hmul gC hgC k sk hNk
  let H : Set (SchemeHomOver (geomPoint k sk) f₀) := {P | FactorsThrough lev₀ P}
  have hone : L₀.one (geomPoint k sk) ∈ H := hlev_one₀ _
  have hmulH : ∀ P Q : SchemeHomOver (geomPoint k sk) f₀, P ∈ H → Q ∈ H → L₀.mul _ P Q ∈ H :=
    fun P Q hP hQ => (hlev_sub₀ _ P Q hP hQ).1
  have hinvH : ∀ P : SchemeHomOver (geomPoint k sk) f₀, P ∈ H → L₀.inv _ P ∈ H := fun P hP => (hlev_sub₀ _ P P hP hP).2
  haveI : NeZero N := ⟨fun h => hNk (by rw [h, Nat.cast_zero])⟩
  have hN : ∀ P : SchemeHomOver (geomPoint k sk) f₀, P ∈ H → L₀.nsmul _ N P = L₀.one _ := fun P hP => by
    rw [G2Asm.nsmul_eq_nsmulPt]; exact hlev_torsion₀ _ P hP
  have hcard : ∀ d : ℕ, d ∣ N → Nat.card {P : ↥H // L₀.nsmul (geomPoint k sk) d P.1 = L₀.one _} = d ^ 2 := by
    intro d hd
    rw [← hcount d hd]
    apply Nat.card_congr
    refine (Equiv.subtypeEquivRight (fun P => ?_)).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter (fun P : SchemeHomOver (geomPoint k sk) f₀ => FactorsThrough lev₀ P)
        (fun P => nsmulPt L₀ (geomPoint k sk) d P = L₀.one (geomPoint k sk)))
    rw [G2Asm.nsmul_eq_nsmulPt]
  have hfin : H.Finite := by
    have h1 : Nat.card {P : ↥H // L₀.nsmul (geomPoint k sk) N P.1 = L₀.one _} ≠ 0 := by
      rw [hcard N dvd_rfl]; exact pow_ne_zero 2 (NeZero.ne N)
    haveI : Finite {P : ↥H // L₀.nsmul (geomPoint k sk) N P.1 = L₀.one _} := Nat.finite_of_card_ne_zero h1
    have e : {P : ↥H // L₀.nsmul (geomPoint k sk) N P.1 = L₀.one _} ≃ ↥H := Equiv.subtypeUnivEquiv (fun P => hN P.1 P.2)
    exact Set.finite_coe_iff.mp (Finite.of_equiv _ e)
  obtain ⟨e, he⟩ := GoodReductionJacobian.RelativeGroupLaw.exists_zmod_prod_equiv_of_natCard_nsmul_eq_one_eq_sq
    L₀ hcomm₀ (geomPoint k sk) H hfin hone hmulH hinvH N hN hcard
  exact ⟨e, he⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_lev_fibre_descend_of_isPullback_of_fg_of_isCommutative
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_lev_fibre_descend_of_isPullback_of_fg_of_isCommutative (solution)
