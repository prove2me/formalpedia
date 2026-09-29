-- Prove2me | solution 1 for CerednikDrinfeld.QM.isFinite_etale_pullback_schemeKer_and_factorsThrough_iff_of_dvd_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/67a11bd6-f68d-5a02-b895-6fef34431972

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_CerednikDrinfeld_QM_isFinite_etale_schemeKerStr_and_etale_isOpenImmersion_of_forall_nsmulPt_eq_one_of_isUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_isFinite_etale_pullback_schemeKer_and_factorsThrough_iff_of_dvd_of_isUnit
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra~schemeHomOverComp GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM"

noncomputable section

namespace SubLevelBody

section Kernel

variable {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)

theorem nsmul_eq_nsmulPt {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (P : SchemeHomOver t f) :
    L.nsmul t n P = nsmulPt L t n P := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show L.mul t (L.nsmul t n P) P = L.mul t (nsmulPt L t n P) P
    rw [ih]

theorem coe_nsmulPt {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (P : SchemeHomOver t f) :
    (nsmulPt L t n P).1 = P.1 ≫ L.schemeNsmul n := by
  have hnat := L.nsmul_natural f t P.1 P.2 n RelativeGroupLaw.idPoint
  have hid : schemeHomOverComp P.1 P.2 (RelativeGroupLaw.idPoint (f := f)) = P :=
    Subtype.ext (Category.comp_id _)
  rw [hid, nsmul_eq_nsmulPt, nsmul_eq_nsmulPt] at hnat
  rw [← hnat]
  show P.1 ≫ (nsmulPt L f n RelativeGroupLaw.idPoint).1 = P.1 ≫ (L.nsmul f n RelativeGroupLaw.idPoint).1
  rw [nsmul_eq_nsmulPt]

theorem coe_one {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) :
    (L.one t).1 = t ≫ (L.one (𝟙 (Spec (CommRingCat.of S)))).1 := by
  have h := L.one_natural (𝟙 _) t t (Category.comp_id t)
  exact (congrArg Subtype.val h).symm

abbrev kerι (n : ℕ) : L.schemeKer n ⟶ A :=
  pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of S)))).1

theorem kerι_f (n : ℕ) : kerι L n ≫ f = L.schemeKerStr n := by
  have h1 : kerι L n ≫ f = kerι L n ≫ (L.schemeNsmul n ≫ f) := by rw [L.schemeNsmul_over n]
  rw [h1, ← Category.assoc, pullback.condition, Category.assoc,
    (L.one (𝟙 (Spec (CommRingCat.of S)))).2, Category.comp_id]

def kerLift {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (n : ℕ) (P : SchemeHomOver t f)
    (hP : nsmulPt L t n P = L.one t) : T ⟶ L.schemeKer n :=
  pullback.lift P.1 t (by rw [← coe_nsmulPt, hP, coe_one])

@[scoped simp, reassoc] theorem kerLift_kerι {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (n : ℕ) (P : SchemeHomOver t f)
    (hP : nsmulPt L t n P = L.one t) : kerLift L n P hP ≫ kerι L n = P.1 :=
  pullback.lift_fst _ _ _

@[scoped simp, reassoc] theorem kerLift_str {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (n : ℕ) (P : SchemeHomOver t f)
    (hP : nsmulPt L t n P = L.one t) : kerLift L n P hP ≫ L.schemeKerStr n = t :=
  pullback.lift_snd _ _ _

end Kernel

section NsmulAlgebra

variable {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)

theorem nsmulPt_eq_pow {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (P : SchemeHomOver t f) :
    letI := L.pointGroup t
    nsmulPt L t n P = P ^ n := by
  letI := L.pointGroup t
  induction n with
  | zero => exact (pow_zero P).symm
  | succ n ih =>
    show L.mul t (nsmulPt L t n P) P = P ^ (n + 1)
    rw [ih, pow_succ]
    rfl

theorem nsmulPt_mul_eq_one {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (d c : ℕ) (P : SchemeHomOver t f)
    (h : nsmulPt L t d P = L.one t) : nsmulPt L t (d * c) P = L.one t := by
  letI := L.pointGroup t
  have h' : P ^ d = 1 := by rw [← nsmulPt_eq_pow L t d P]; exact h
  rw [nsmulPt_eq_pow L t (d * c) P, pow_mul, h', one_pow]
  rfl

theorem nsmulPt_eq_one_of_factorsThrough_kerι {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (d : ℕ)
    (P : SchemeHomOver t f) (h : FactorsThrough (kerι L d) P) : nsmulPt L t d P = L.one t := by
  obtain ⟨P₀, hP₀⟩ := h
  apply Subtype.ext
  rw [coe_nsmulPt, coe_one, ← hP₀, Category.assoc, pullback.condition, ← Category.assoc]
  congr 1

  show P₀ ≫ L.schemeKerStr d = t
  rw [← kerι_f, ← Category.assoc, hP₀]
  exact P.2

end NsmulAlgebra

section SubLevel

variable {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
  (L : RelativeGroupLaw S f) (hcomm : L.IsCommutative) (hbundle : AbelianSchemePropertyBundle S f)
  {C : Scheme.{0}} (lev : C ⟶ A) (hlev_closed : IsClosedImmersion lev) (N : ℕ)
  (hlev_torsion : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f),
    FactorsThrough lev P → nsmulPt L t N P = L.one t)
  (hlev_flat : Flat (lev ≫ f)) (hlev_fp : LocallyOfFinitePresentation (lev ≫ f))
  (hN : IsUnit ((N : ℕ) : S)) (d : ℕ) (hd : d ∣ N)

include hd hN in
theorem isUnit_d : IsUnit ((d : ℕ) : S) := by
  obtain ⟨c, rfl⟩ := hd
  push_cast at hN
  exact isUnit_of_mul_isUnit_left hN

theorem isClosedImmersion_one (hbundle : AbelianSchemePropertyBundle S f) :
    IsClosedImmersion (L.one (𝟙 (Spec (CommRingCat.of S)))).1 := by
  haveI : IsProper f := hbundle.proper
  have he : (L.one (𝟙 _)).1 ≫ f = 𝟙 _ := (L.one (𝟙 _)).2
  have : IsClosedImmersion ((L.one (𝟙 _)).1 ≫ f) := by rw [he]; infer_instance
  exact IsClosedImmersion.of_comp _ f

include hbundle in
theorem isClosedImmersion_kerι (n : ℕ) : IsClosedImmersion (kerι L n) := by
  haveI := isClosedImmersion_one L hbundle
  show IsClosedImmersion (pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of S)))).1)
  infer_instance

theorem nsmulPt_eq_one_of_factorsThrough_one {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ)
    (P : SchemeHomOver t f) (h : FactorsThrough (L.one (𝟙 (Spec (CommRingCat.of S)))).1 P) :
    nsmulPt L t n P = L.one t := by
  obtain ⟨P₀, hP₀⟩ := h
  have hP₀t : P₀ = t := by
    have h2 := P.2
    rw [← hP₀, Category.assoc, (L.one (𝟙 (Spec (CommRingCat.of S)))).2, Category.comp_id] at h2
    exact h2
  have hP : P = L.one t := Subtype.ext (by rw [coe_one, ← hP₀, hP₀t])
  letI := L.pointGroup t
  rw [hP, nsmulPt_eq_pow]
  exact one_pow n

include hcomm hbundle hlev_closed hlev_torsion hlev_flat hlev_fp hN hd in

theorem main :
    IsFinite (pullback.fst lev (kerι L d) ≫ lev ≫ f) ∧ Etale (pullback.fst lev (kerι L d) ≫ lev ≫ f) ∧
    IsOpenImmersion (pullback.fst lev (kerι L d)) ∧
    ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f),
      FactorsThrough (pullback.fst lev (kerι L d) ≫ lev) P ↔ FactorsThrough lev P ∧ nsmulPt L t d P = L.one t := by
  have hdU := isUnit_d N hN d hd
  have he : (L.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ f = 𝟙 _ := (L.one (𝟙 _)).2

  obtain ⟨hdfin, hdet, -, -⟩ :=
    CerednikDrinfeld.QM.isFinite_etale_schemeKerStr_and_etale_isOpenImmersion_of_forall_nsmulPt_eq_one_of_isUnit
      L hcomm hbundle (L.one (𝟙 (Spec (CommRingCat.of S)))).1 (isClosedImmersion_one L hbundle) d
      (fun t P h => nsmulPt_eq_one_of_factorsThrough_one L t d P h)
      (by rw [he]; infer_instance) (by rw [he]; infer_instance) hdU

  obtain ⟨-, hNet, hCet, wC, hjopen⟩ :=
    CerednikDrinfeld.QM.isFinite_etale_schemeKerStr_and_etale_isOpenImmersion_of_forall_nsmulPt_eq_one_of_isUnit
      L hcomm hbundle lev hlev_closed N hlev_torsion hlev_flat hlev_fp hN

  have hflat_d : Flat (kerι L d ≫ f) := by rw [kerι_f]; haveI := hdet; infer_instance
  have hfp_d : LocallyOfFinitePresentation (kerι L d ≫ f) := by rw [kerι_f]; haveI := hdet; infer_instance
  have htorN : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f),
      FactorsThrough (kerι L d) P → nsmulPt L t N P = L.one t := by
    intro T t P h
    obtain ⟨c, hc⟩ := hd
    rw [hc]
    exact nsmulPt_mul_eq_one L t d c P (nsmulPt_eq_one_of_factorsThrough_kerι L t d P h)
  obtain ⟨-, -, -, wd, hiopen⟩ :=
    CerednikDrinfeld.QM.isFinite_etale_schemeKerStr_and_etale_isOpenImmersion_of_forall_nsmulPt_eq_one_of_isUnit
      L hcomm hbundle (kerι L d) (isClosedImmersion_kerι L hbundle d) N htorN hflat_d hfp_d hN

  obtain ⟨j, hj⟩ : ∃ j : C ⟶ L.schemeKer N, j = pullback.lift lev (lev ≫ f) wC := ⟨_, rfl⟩
  obtain ⟨i, hi⟩ : ∃ i : L.schemeKer d ⟶ L.schemeKer N, i = pullback.lift (kerι L d) (kerι L d ≫ f) wd := ⟨_, rfl⟩
  rw [← hj] at hjopen
  rw [← hi] at hiopen
  haveI := hjopen
  haveI := hiopen
  have hjι : j ≫ kerι L N = lev := by rw [hj]; exact pullback.lift_fst _ _ _
  have hiι : i ≫ kerι L N = kerι L d := by rw [hi]; exact pullback.lift_fst _ _ _
  haveI : Mono (kerι L N) := by haveI := isClosedImmersion_kerι L hbundle N; infer_instance
  have hsq : pullback.fst lev (kerι L d) ≫ j = pullback.snd lev (kerι L d) ≫ i := by
    rw [← cancel_mono (kerι L N), Category.assoc, Category.assoc, hjι, hiι, pullback.condition]
  have hsq' : pullback.fst j i ≫ lev = pullback.snd j i ≫ kerι L d := by
    rw [← hjι, ← hiι, ← Category.assoc, pullback.condition, Category.assoc]
  obtain ⟨v, hv⟩ : ∃ v : pullback lev (kerι L d) ⟶ pullback j i,
      v = pullback.lift (pullback.fst lev (kerι L d)) (pullback.snd lev (kerι L d)) hsq := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : pullback j i ⟶ pullback lev (kerι L d),
      u = pullback.lift (pullback.fst j i) (pullback.snd j i) hsq' := ⟨_, rfl⟩
  have hv1 : v ≫ pullback.fst j i = pullback.fst lev (kerι L d) := by rw [hv, pullback.lift_fst]
  have hv2 : v ≫ pullback.snd j i = pullback.snd lev (kerι L d) := by rw [hv, pullback.lift_snd]
  have hu1 : u ≫ pullback.fst lev (kerι L d) = pullback.fst j i := by rw [hu, pullback.lift_fst]
  have hu2 : u ≫ pullback.snd lev (kerι L d) = pullback.snd j i := by rw [hu, pullback.lift_snd]
  have huv : u ≫ v = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hv1, hu1, Category.id_comp]
    · rw [Category.assoc, hv2, hu2, Category.id_comp]
  have hvu : v ≫ u = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hu1, hv1, Category.id_comp]
    · rw [Category.assoc, hu2, hv2, Category.id_comp]
  haveI : IsIso v := ⟨⟨u, hvu, huv⟩⟩
  have hfst : pullback.fst lev (kerι L d) = v ≫ pullback.fst j i := hv1.symm

  have hopen : IsOpenImmersion (pullback.fst lev (kerι L d)) := by
    rw [hfst]; infer_instance
  haveI := hopen
  haveI := hCet
  refine ⟨?_, inferInstance, hopen, fun t P => ?_⟩
  ·
    have hre : pullback.fst lev (kerι L d) ≫ lev ≫ f = pullback.snd lev (kerι L d) ≫ L.schemeKerStr d := by
      rw [← kerι_f, ← Category.assoc, pullback.condition, Category.assoc]
    rw [hre]
    haveI := hlev_closed
    haveI := hdfin
    haveI : IsClosedImmersion (pullback.snd lev (kerι L d)) := inferInstance
    infer_instance
  · constructor
    · rintro ⟨P₀, hP₀⟩
      refine ⟨⟨P₀ ≫ pullback.fst lev (kerι L d), by rw [Category.assoc]; exact hP₀⟩, ?_⟩
      refine nsmulPt_eq_one_of_factorsThrough_kerι L t d P ⟨P₀ ≫ pullback.snd lev (kerι L d), ?_⟩
      rw [Category.assoc, ← pullback.condition, ← Category.assoc]
      rw [← Category.assoc] at hP₀
      exact hP₀
    · rintro ⟨⟨Q₀, hQ₀⟩, htor⟩
      refine ⟨pullback.lift Q₀ (kerLift L d P htor) (by rw [hQ₀, kerLift_kerι]), ?_⟩
      rw [← Category.assoc, pullback.lift_fst, hQ₀]

end SubLevel
end SubLevelBody
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_isFinite_etale_pullback_schemeKer_and_factorsThrough_iff_of_dvd_of_isUnit.SubLevelBody"

open SubLevelBody in

theorem solution
    {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hcomm : L.IsCommutative) (hbundle : AbelianSchemePropertyBundle S f)
    {C : Scheme.{0}} (lev : C ⟶ A) (hlev_closed : IsClosedImmersion lev) (N : ℕ)
    (hlev_torsion : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f),
      FactorsThrough lev P → nsmulPt L t N P = L.one t)
    (hlev_flat : Flat (lev ≫ f)) (hlev_fp : LocallyOfFinitePresentation (lev ≫ f))
    (hN : IsUnit ((N : ℕ) : S)) (d : ℕ) (hd : d ∣ N) :
    IsFinite (pullback.fst lev (pullback.fst (L.schemeNsmul d) (L.one (𝟙 (Spec (CommRingCat.of S)))).1) ≫ lev ≫ f) ∧
    Etale (pullback.fst lev (pullback.fst (L.schemeNsmul d) (L.one (𝟙 (Spec (CommRingCat.of S)))).1) ≫ lev ≫ f) ∧
    IsOpenImmersion (pullback.fst lev (pullback.fst (L.schemeNsmul d) (L.one (𝟙 (Spec (CommRingCat.of S)))).1)) ∧
    ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f),
      FactorsThrough (pullback.fst lev (pullback.fst (L.schemeNsmul d) (L.one (𝟙 (Spec (CommRingCat.of S)))).1) ≫ lev) P ↔
        FactorsThrough lev P ∧ nsmulPt L t d P = L.one t :=
  SubLevelBody.main L hcomm hbundle lev hlev_closed N hlev_torsion hlev_flat hlev_fp hN d hd

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_isFinite_etale_pullback_schemeKer_and_factorsThrough_iff_of_dvd_of_isUnit.SubLevelBody"

end S_CerednikDrinfeld_QM_isFinite_etale_pullback_schemeKer_and_factorsThrough_iff_of_dvd_of_isUnit
end P2MW
export P2MW.S_CerednikDrinfeld_QM_isFinite_etale_pullback_schemeKer_and_factorsThrough_iff_of_dvd_of_isUnit (solution)
