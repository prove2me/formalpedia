-- Prove2me | solution 1 for CerednikDrinfeld.QM.isFinite_etale_schemeKerStr_and_etale_isOpenImmersion_of_forall_nsmulPt_eq_one_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/f15a04a0-13fe-5eb6-8858-a355c453e1f1

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_etale_schemeNsmul_of_isUnit_of_smoothOfRelativeDimension
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isPullback_schemeNsmul_baseChange_and_of_isStableUnderBaseChange
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_smoothOfRelativeDimension_of_smooth_of_isLocalRing
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_pullback_snd_schemeKerStr_of_isUnit
import Theorems.Thm_AlgebraicGeometry_Etale_of_forall_pullback_snd_localization_atPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_isFinite_etale_schemeKerStr_and_etale_isOpenImmersion_of_forall_nsmulPt_eq_one_of_isUnit

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM

noncomputable section

universe u

namespace TorsFinEt10

theorem lfp_of_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : LocallyOfFinitePresentation (f ≫ g)) (hg : LocallyOfFiniteType g) : LocallyOfFinitePresentation f := by
  wlog hZ : IsAffine Z generalizing X Y Z
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation) _
      (g.iSup_preimage_eq_top (iSup_affineOpens_eq_top Z))]
    intro U
    have H := IsZariskiLocalAtTarget.restrict h U.1
    rw [morphismRestrict_comp] at H
    exact this _ _ H inferInstance inferInstance
  wlog hY : IsAffine Y generalizing X Y
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation) _ (iSup_affineOpens_eq_top Y)]
    intro U
    have H : LocallyOfFinitePresentation ((f ⁻¹ᵁ U.1).ι ≫ f ≫ g) := inferInstance
    rw [← morphismRestrict_ι_assoc] at H
    exact this _ _ H inferInstance inferInstance
  wlog hX : IsAffine X generalizing X
  · rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation) _ (iSup_affineOpens_eq_top X)]
    intro U
    have H : LocallyOfFinitePresentation (U.1.ι ≫ f ≫ g) := inferInstance
    rw [← Category.assoc] at H
    exact this _ H inferInstance
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)] at h ⊢
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)] at hg
  rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] at h
  exact RingHom.FinitePresentation.of_comp_finiteType _ h hg

theorem comp_one {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (t' : T' ⟶ Spec (CommRingCat.of S)) (ψ : T' ⟶ T)
    (hψ : ψ ≫ t = t') : ψ ≫ (L.one t).1 = (L.one t').1 := by
  have hm := L.mul_natural t t' ψ hψ

  have h : schemeHomOverComp ψ hψ (L.one t) =
      L.mul t' (schemeHomOverComp ψ hψ (L.one t)) (schemeHomOverComp ψ hψ (L.one t)) := by
    conv_lhs => rw [← L.one_mul t (L.one t)]
    exact hm _ _
  have : schemeHomOverComp ψ hψ (L.one t) = L.one t' := by
    calc schemeHomOverComp ψ hψ (L.one t)
        = L.mul t' (L.one t') (schemeHomOverComp ψ hψ (L.one t)) := (L.one_mul t' _).symm
      _ = L.mul t' (L.mul t' (L.inv t' (schemeHomOverComp ψ hψ (L.one t))) (schemeHomOverComp ψ hψ (L.one t)))
            (schemeHomOverComp ψ hψ (L.one t)) := by rw [L.inv_mul_cancel]
      _ = L.mul t' (L.inv t' (schemeHomOverComp ψ hψ (L.one t)))
            (L.mul t' (schemeHomOverComp ψ hψ (L.one t)) (schemeHomOverComp ψ hψ (L.one t))) := by rw [L.mul_assoc]
      _ = L.mul t' (L.inv t' (schemeHomOverComp ψ hψ (L.one t))) (schemeHomOverComp ψ hψ (L.one t)) := by rw [← h]
      _ = L.one t' := L.inv_mul_cancel t' _
  exact congrArg Subtype.val this

end TorsFinEt10

namespace LevEtaleBare

theorem isFinite_and_etale_schemeKerStr {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hcomm : L.IsCommutative) (hbundle : AbelianSchemePropertyBundle S f)
    (m : ℕ) (hm : IsUnit ((m : ℕ) : S)) :
    IsFinite (L.schemeKerStr m) ∧ Etale (L.schemeKerStr m) := by
  classical
  have hsm : Smooth f := hbundle.smooth
  have hpr : IsProper f := hbundle.proper

  have he : (L.one (𝟙 _)).1 ≫ f = 𝟙 _ := (L.one (𝟙 _)).2
  haveI : IsClosedImmersion (L.one (𝟙 (Spec (CommRingCat.of S)))).1 := by
    have : IsClosedImmersion ((L.one (𝟙 _)).1 ≫ f) := by rw [he]; infer_instance
    exact IsClosedImmersion.of_comp _ f
  have hnA_over : L.schemeNsmul m ≫ f = f := L.schemeNsmul_over m
  haveI : LocallyOfFinitePresentation (L.schemeNsmul m) :=
    TorsFinEt10.lfp_of_comp (L.schemeNsmul m) f (by rw [hnA_over]; infer_instance) inferInstance
  haveI : LocallyOfFinitePresentation (L.schemeKerStr m) := by
    show LocallyOfFinitePresentation (pullback.snd (L.schemeNsmul m) (L.one (𝟙 _)).1)
    infer_instance

  have hκ : L.schemeKerStr m = pullback.fst (L.schemeNsmul m) (L.one (𝟙 _)).1 ≫ f := by
    show pullback.snd (L.schemeNsmul m) (L.one (𝟙 _)).1 = _
    have h1 : pullback.fst (L.schemeNsmul m) (L.one (𝟙 _)).1 ≫ f =
        pullback.fst (L.schemeNsmul m) (L.one (𝟙 _)).1 ≫ (L.schemeNsmul m ≫ f) := by rw [hnA_over]
    rw [h1, ← Category.assoc, pullback.condition, Category.assoc, he, Category.comp_id]
  haveI : IsProper (L.schemeKerStr m) := by rw [hκ]; infer_instance

  have hEt : Etale (L.schemeKerStr m) := by
    refine AlgebraicGeometry.Etale.of_forall_pullback_snd_localization_atPrime (L.schemeKerStr m) (fun p _ => ?_)
    let ι : Spec (CommRingCat.of (Localization.AtPrime p)) ⟶ Spec (CommRingCat.of S) :=
      Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime p)))
    let G' := L.baseChange ι
    haveI : Smooth (RelativeGroupLaw.baseChangeStr ι f) := by
      show Smooth (pullback.snd f ι); infer_instance
    obtain ⟨d, hd⟩ := GoodReductionJacobian.RelativeGroupLaw.exists_smoothOfRelativeDimension_of_smooth_of_isLocalRing G'
    haveI := hd
    have hm' : IsUnit ((m : ℕ) : Localization.AtPrime p) := by
      simpa using hm.map (algebraMap S (Localization.AtPrime p))
    haveI hEt' : Etale (G'.schemeNsmul m) :=
      GoodReductionJacobian.RelativeGroupLaw.etale_schemeNsmul_of_isUnit_of_smoothOfRelativeDimension G'
        (fun t x y => (RelativeGroupLaw.IsCommutative.baseChange ι hcomm) t x y) d m hm'

    obtain ⟨hsq, -⟩ :=
      GoodReductionJacobian.RelativeGroupLaw.isPullback_schemeNsmul_baseChange_and_of_isStableUnderBaseChange ι L m

    have he' : (G'.one (𝟙 _)).1 ≫ pullback.fst f ι = ι ≫ (L.one (𝟙 _)).1 := by
      show ((L.baseChange ι).one (𝟙 _)).1 ≫ pullback.fst f ι = ι ≫ (L.one (𝟙 _)).1
      rw [RelativeGroupLaw.baseChange_one, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst]
      exact (TorsFinEt10.comp_one L (𝟙 _) (𝟙 _ ≫ ι) ι (by simp)).symm

    have hbig : IsPullback (pullback.fst (G'.schemeNsmul m) (G'.one (𝟙 _)).1 ≫ pullback.fst f ι)
        (pullback.snd (G'.schemeNsmul m) (G'.one (𝟙 _)).1) (L.schemeNsmul m) (ι ≫ (L.one (𝟙 _)).1) := by
      rw [← he']
      exact IsPullback.paste_horiz (IsPullback.of_hasPullback _ _) hsq
    have e1 : pullback.snd (L.schemeKerStr m) ι =
        (pullbackLeftPullbackSndIso (L.schemeNsmul m) (L.one (𝟙 _)).1 ι).hom ≫ hbig.isoPullback.inv ≫
          pullback.snd (G'.schemeNsmul m) (G'.one (𝟙 _)).1 := by
      rw [hbig.isoPullback_inv_snd, pullbackLeftPullbackSndIso_hom_snd]
    rw [e1]
    infer_instance

  haveI : LocallyQuasiFinite (L.schemeKerStr m) := by
    refine LocallyQuasiFinite.of_fiberToSpecResidueField _ (fun x => ?_)
    obtain ⟨φ, hφ⟩ := Spec.map_surjective ((Spec (CommRingCat.of S)).fromSpecResidueField x)
    have hmx : IsUnit ((m : ℕ) : ↑((Spec (CommRingCat.of S)).residueField x)) := by
      simpa using hm.map φ.hom
    have := GoodReductionJacobian.RelativeGroupLaw.locallyQuasiFinite_pullback_snd_schemeKerStr_of_isUnit
      ((Spec (CommRingCat.of S)).fromSpecResidueField x) L (fun t x y => hcomm t x y) m hmx
    exact this
  exact ⟨IsFinite.of_isProper_of_locallyQuasiFinite _, hEt⟩

end LevEtaleBare

namespace LevEtaleCritBody

section Geometric

variable {S : Type} [CommRing S]

def ringHomOf {k : Type} [Field k] (b : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of S)) : S →+* k :=
  (Spec.preimage b).hom

theorem geomPoint_ringHomOf {k : Type} [Field k] (b : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of S)) :
    geomPoint k (ringHomOf b) = b := by
  unfold geomPoint ringHomOf
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]

def geomPtAt (X : Scheme.{0}) (x : X) : Spec (CommRingCat.of (AlgebraicClosure (X.residueField x))) ⟶ X :=
  Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) (AlgebraicClosure (X.residueField x)))) ≫
    X.fromSpecResidueField x

theorem geomPtAt_apply (X : Scheme.{0}) (x : X) (p : Spec (CommRingCat.of (AlgebraicClosure (X.residueField x)))) :
    (geomPtAt X x).base p = x := by
  simp only [geomPtAt, Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply]
  exact Scheme.fromSpecResidueField_apply x _

end Geometric

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

section Level

variable {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
  (L : RelativeGroupLaw S f) {C : Scheme.{0}} (lev : C ⟶ A) (N : ℕ)
  (hlev_torsion : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f),
    FactorsThrough lev P → nsmulPt L t N P = L.one t)

def tautPt : SchemeHomOver (lev ≫ f) f := ⟨lev, rfl⟩

include hlev_torsion in
theorem tautPt_torsion : nsmulPt L (lev ≫ f) N (tautPt lev) = L.one _ :=
  hlev_torsion _ _ ⟨𝟙 _, Category.id_comp _⟩

include hlev_torsion in

theorem lev_schemeNsmul : lev ≫ L.schemeNsmul N = (lev ≫ f) ≫ (L.one (𝟙 (Spec (CommRingCat.of S)))).1 := by
  rw [← coe_one L (lev ≫ f), ← tautPt_torsion L lev N hlev_torsion, coe_nsmulPt]
  rfl

def jC (w : lev ≫ L.schemeNsmul N = (lev ≫ f) ≫ (L.one (𝟙 (Spec (CommRingCat.of S)))).1) : C ⟶ L.schemeKer N :=
  pullback.lift lev (lev ≫ f) w

variable (w : lev ≫ L.schemeNsmul N = (lev ≫ f) ≫ (L.one (𝟙 (Spec (CommRingCat.of S)))).1)

@[scoped simp, reassoc] theorem jC_kerι : jC L lev N w ≫ kerι L N = lev := pullback.lift_fst _ _ _

@[scoped simp, reassoc] theorem jC_str : jC L lev N w ≫ L.schemeKerStr N = lev ≫ f := pullback.lift_snd _ _ _

theorem isClosedImmersion_jC (hlev_closed : IsClosedImmersion lev) : IsClosedImmersion (jC L lev N w) := by
  haveI : IsClosedImmersion (jC L lev N w ≫ kerι L N) := by rw [jC_kerι]; exact hlev_closed
  exact IsClosedImmersion.of_comp (jC L lev N w) (kerι L N)

include w in

theorem etale_lev_f (hlev_closed : IsClosedImmersion lev) (hlev_flat : Flat (lev ≫ f))
    (hlev_fp : LocallyOfFinitePresentation (lev ≫ f)) (het : Etale (L.schemeKerStr N)) : Etale (lev ≫ f) := by
  haveI := het
  haveI := isClosedImmersion_jC L lev N w hlev_closed
  haveI : FormallyUnramified (lev ≫ f) := by
    rw [← jC_str L lev N w]
    exact MorphismProperty.comp_mem _ _ _ (inferInstance : FormallyUnramified (jC L lev N w))
      (inferInstance : FormallyUnramified (L.schemeKerStr N))
  haveI := hlev_flat
  haveI := hlev_fp
  exact Etale.of_formallyUnramified_of_flat _

theorem isOpenImmersion_jC (hlev_closed : IsClosedImmersion lev) (hlev_flat : Flat (lev ≫ f))
    (hlev_fp : LocallyOfFinitePresentation (lev ≫ f)) (het : Etale (L.schemeKerStr N)) :
    IsOpenImmersion (jC L lev N w) := by
  haveI := het
  haveI : Etale (jC L lev N w ≫ L.schemeKerStr N) := by
    rw [jC_str]; exact etale_lev_f L lev N w hlev_closed hlev_flat hlev_fp het
  haveI : Etale (jC L lev N w) := Etale.of_comp (jC L lev N w) (L.schemeKerStr N)
  haveI : Mono (jC L lev N w) := by
    haveI := hlev_closed
    exact mono_of_mono_fac (jC_kerι L lev N w)
  exact IsOpenImmersion.of_flat_of_mono _

end Level

end LevEtaleCritBody
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_isFinite_etale_schemeKerStr_and_etale_isOpenImmersion_of_forall_nsmulPt_eq_one_of_isUnit.LevEtaleCritBody"

theorem solution
    {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hcomm : L.IsCommutative) (hbundle : AbelianSchemePropertyBundle S f)
    {C : Scheme.{0}} (lev : C ⟶ A) (hlev_closed : IsClosedImmersion lev) (N : ℕ)
    (hlev_torsion : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f),
      FactorsThrough lev P → nsmulPt L t N P = L.one t)
    (hlev_flat : Flat (lev ≫ f)) (hlev_fp : LocallyOfFinitePresentation (lev ≫ f))
    (hN : IsUnit ((N : ℕ) : S)) :
    IsFinite (L.schemeKerStr N) ∧ Etale (L.schemeKerStr N) ∧ Etale (lev ≫ f) ∧
      ∃ w : lev ≫ L.schemeNsmul N = (lev ≫ f) ≫ (L.one (𝟙 (Spec (CommRingCat.of S)))).1,
        IsOpenImmersion (pullback.lift lev (lev ≫ f) w) := by
  obtain ⟨hfin, het⟩ := LevEtaleBare.isFinite_and_etale_schemeKerStr L hcomm hbundle N hN
  have w := LevEtaleCritBody.lev_schemeNsmul L lev N hlev_torsion
  exact ⟨hfin, het, LevEtaleCritBody.etale_lev_f L lev N w hlev_closed hlev_flat hlev_fp het,
    w, LevEtaleCritBody.isOpenImmersion_jC L lev N w hlev_closed hlev_flat hlev_fp het⟩

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_isFinite_etale_schemeKerStr_and_etale_isOpenImmersion_of_forall_nsmulPt_eq_one_of_isUnit.LevEtaleCritBody"

end S_CerednikDrinfeld_QM_isFinite_etale_schemeKerStr_and_etale_isOpenImmersion_of_forall_nsmulPt_eq_one_of_isUnit
end P2MW
export P2MW.S_CerednikDrinfeld_QM_isFinite_etale_schemeKerStr_and_etale_isOpenImmersion_of_forall_nsmulPt_eq_one_of_isUnit (solution)
