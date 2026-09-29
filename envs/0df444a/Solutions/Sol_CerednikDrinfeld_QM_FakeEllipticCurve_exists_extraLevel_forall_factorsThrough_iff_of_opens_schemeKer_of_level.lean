-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_forall_factorsThrough_iff_of_opens_schemeKer_of_level
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/02eae633-6c5d-5086-8d25-1dd6dd052a70

import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isFinite_and_etale_schemeKerStr_of_isUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_forall_factorsThrough_iff_of_opens_schemeKer_of_level
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra~schemeHomOverComp GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM"
open scoped Quaternion

namespace ExtraLevelOfClopen21

variable {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)

theorem nsmul_eq_nsmulPt {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) :
    L.nsmul t n x = nsmulPt L t n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show L.mul t (L.nsmul t n x) x = L.mul t (nsmulPt L t n x) x
    rw [ih]

theorem nsmulPt_val {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t f) :
    (nsmulPt L t n P).1 = P.1 ≫ L.schemeNsmul n := by
  rw [← nsmul_eq_nsmulPt]
  have hnat := L.nsmul_natural f t P.1 P.2 n RelativeGroupLaw.idPoint
  have hid : schemeHomOverComp P.1 P.2 (RelativeGroupLaw.idPoint : SchemeHomOver f f) = P :=
    Subtype.ext (Category.comp_id _)
  rw [hid] at hnat
  rw [← hnat]
  rfl

theorem fst_comp_eq_schemeKerStr (n : ℕ) :
    pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f = L.schemeKerStr n := by
  calc pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f
      = pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ (L.schemeNsmul n ≫ f) := by
        rw [L.schemeNsmul_over]
    _ = (pullback.snd (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫
          (L.one (𝟙 (Spec (CommRingCat.of R)))).1) ≫ f := by rw [← Category.assoc, pullback.condition]
    _ = L.schemeKerStr n := by
        rw [Category.assoc, (L.one (𝟙 (Spec (CommRingCat.of R)))).2, Category.comp_id]

theorem nsmulPt_eq_one_of_factorsThrough (n : ℕ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (P : SchemeHomOver t f)
    (hP : FactorsThrough (pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1) P) :
    nsmulPt L t n P = L.one t := by
  obtain ⟨P₀, hP₀⟩ := hP
  apply Subtype.ext
  rw [nsmulPt_val, ← hP₀, Category.assoc, pullback.condition, ← Category.assoc]
  have ht : P₀ ≫ pullback.snd (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 = t := by
    rw [← P.2, ← hP₀, Category.assoc, fst_comp_eq_schemeKerStr]
  rw [ht]
  have h1 := L.one_natural (𝟙 (Spec (CommRingCat.of R))) t t (Category.comp_id _)
  exact (congrArg Subtype.val h1 : _)

end ExtraLevelOfClopen21

open ExtraLevelOfClopen21 in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N₀ : ℕ} {S : Type} [CommRing S]
    (E : FakeEllipticCurve Λ N₀ S) (N : ℕ) [NeZero N] (hN : IsUnit ((N : ℕ) : S))
    (U : (E.L.schemeKer N).Opens) (hUc : IsClosed (U : Set ↥(E.L.schemeKer N)))
    (hsub : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      FactorsThrough (U.ι ≫ pullback.fst (E.L.schemeNsmul N) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1) P →
      FactorsThrough (U.ι ≫ pullback.fst (E.L.schemeNsmul N) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1) Q →
        FactorsThrough (U.ι ≫ pullback.fst (E.L.schemeNsmul N) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1)
            (E.L.mul t P Q) ∧
          FactorsThrough (U.ι ≫ pullback.fst (E.L.schemeNsmul N) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1)
            (E.L.inv t P))
    (hone : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)),
      FactorsThrough (U.ι ≫ pullback.fst (E.L.schemeNsmul N) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1)
        (E.L.one t))
    (hstab : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      FactorsThrough (U.ι ≫ pullback.fst (E.L.schemeNsmul N) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1) P →
        FactorsThrough (U.ι ≫ pullback.fst (E.L.schemeNsmul N) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1)
          (pushPt (E.act x) (E.act_over x) P))
    (hdisj : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      FactorsThrough (U.ι ≫ pullback.fst (E.L.schemeNsmul N) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1) P →
        FactorsThrough E.lev P → P = E.L.one t)
    (hrank : ∀ s : ↥(Spec (CommRingCat.of S)), (U.ι ≫ E.L.schemeKerStr N).finrank s = N ^ 2)
    (hfib : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k), (N : k) ≠ 0 →
      ∃ e : ZMod N × ZMod N ≃
          {P : SchemeHomOver (geomPoint k sk) E.f //
            FactorsThrough (U.ι ≫ pullback.fst (E.L.schemeNsmul N) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1) P},
        ∀ x y : ZMod N × ZMod N,
          (e (x + y) : SchemeHomOver (geomPoint k sk) E.f) = E.L.mul (geomPoint k sk) (e x) (e y)) :
    ∃ K : E.ExtraLevel N,
      ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
        FactorsThrough K.levK P ↔
          FactorsThrough (U.ι ≫ pullback.fst (E.L.schemeNsmul N) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1) P := by
  classical
  set ι : E.L.schemeKer N ⟶ E.A := pullback.fst (E.L.schemeNsmul N) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1 with hι
  obtain ⟨hfinK, hetK⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.isFinite_and_etale_schemeKerStr_of_isUnit E N hN
  haveI := hfinK; haveI := hetK
  have hιf : ι ≫ E.f = E.L.schemeKerStr N := fst_comp_eq_schemeKerStr E.L N
  have hlev : (U.ι ≫ ι) ≫ E.f = U.ι ≫ E.L.schemeKerStr N := by rw [Category.assoc, hιf]

  haveI : IsSeparated E.f := by haveI := E.bundle.proper; infer_instance
  haveI : IsClosedImmersion (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1 := by
    have : IsClosedImmersion ((E.L.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ E.f) := by
      rw [(E.L.one (𝟙 (Spec (CommRingCat.of S)))).2]; infer_instance
    exact IsClosedImmersion.of_comp _ E.f
  haveI : IsClosedImmersion ι := by rw [hι]; infer_instance
  haveI : IsClosedImmersion U.ι :=
    IsClosedImmersion.of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hUc)
  have htor : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      FactorsThrough (U.ι ≫ ι) P → nsmulPt E.L t N P = E.L.one t := by
    intro T t P hP
    obtain ⟨P₀, hP₀⟩ := hP
    exact nsmulPt_eq_one_of_factorsThrough E.L N t P ⟨P₀ ≫ U.ι, by rw [Category.assoc]; exact hP₀⟩
  have hdisj' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      FactorsThrough (U.ι ≫ ι) P → FactorsThrough E.lev P → P = E.L.one t :=
    fun t P hU hC => hdisj t P hU hC
  have hfin : IsFinite ((U.ι ≫ ι) ≫ E.f) := by rw [hlev]; infer_instance
  have hflat : Flat ((U.ι ≫ ι) ≫ E.f) := by rw [hlev]; infer_instance
  have hlfp : LocallyOfFinitePresentation ((U.ι ≫ ι) ≫ E.f) := by rw [hlev]; infer_instance
  have hrk : ∀ s : ↥(Spec (CommRingCat.of S)), ((U.ι ≫ ι) ≫ E.f).finrank s = N ^ 2 := by
    intro s; rw [hlev]; exact hrank s
  exact ⟨⟨(U : Scheme.{0}), U.ι ≫ ι, inferInstance, hsub, hone, htor, hstab, hdisj', hfin, hflat, hlfp, hrk, hfib⟩,
    fun t P => Iff.rfl⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_forall_factorsThrough_iff_of_opens_schemeKer_of_level
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_forall_factorsThrough_iff_of_opens_schemeKer_of_level (solution)
