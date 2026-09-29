-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.forall_mapPt_eq_one_of_forall_rationalPoint
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/f64ad2ca-ef58-534f-8007-e712d6305005

import Definitions.Def_CerednikDrinfeld_QMModuli
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isReduced_pullback_one_of_natCast_ne_zero
import Theorems.Thm_CerednikDrinfeld_QM_exists_comp_eq_of_forall_factorsThrough_of_isReduced
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_forall_mapPt_eq_one_of_forall_rationalPoint
p2m_attr_erase "instance" "GoodReductionJacobian.RelativeGroupLaw.isIso_endKerStr_schemeHomOverId"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.schemeHomOverNpow_succ NeronModelInfra.schemeHomOverNpow_zero NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

namespace KerPts

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem one_comp_val (G : RelativeGroupLaw R f) {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) : ψ ≫ (G.one t).1 = (G.one (ψ ≫ t)).1 :=
  congrArg Subtype.val (G.one_natural t (ψ ≫ t) ψ rfl)

theorem one_val_congr (G : RelativeGroupLaw R f) {T : Scheme.{u}} (s s' : T ⟶ Spec (CommRingCat.of R)) (h : s = s') :
    (G.one s).1 = (G.one s').1 := by
  subst h; rfl

end KerPts

open KerPts in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (k : Type u) [Field k] [IsAlgClosed k]
    (E E' E'' : FakeEllipticCurve Λ N k) (n : ℕ) (hnk : (n : k) ≠ 0)
    (φ' : E.A ⟶ E'.A) (hφ' : φ' ≫ E'.f = E.f)
    (hφ'mul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E.f),
      mapPt φ' hφ' (E.L.mul t P Q) = E'.L.mul t (mapPt φ' hφ' P) (mapPt φ' hφ' Q))
    (hφ'act : ∀ x : ↥Λ, E.act x ≫ φ' = φ' ≫ E'.act x)
    (ψ' : E'.A ⟶ E.A) (hψ' : ψ' ≫ E.f = E'.f)
    (hψ'φ' : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E.f),
      mapPt ψ' hψ' (mapPt φ' hφ' P) = nsmulPt E.L t n P)
    (hφ'ψ' : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t E'.f),
      mapPt φ' hφ' (mapPt ψ' hψ' Q) = nsmulPt E'.L t n Q)
    (φ'' : E.A ⟶ E''.A) (hφ'' : φ'' ≫ E''.f = E.f)
    (hpts : ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f,
      mapPt φ' hφ' P = E'.L.one _ → mapPt φ'' hφ'' P = E''.L.one _) :
    ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E.f),
      mapPt φ' hφ' P = E'.L.one t → mapPt φ'' hφ'' P = E''.L.one t := by
  intro T t P hP

  have hKR :=
    CerednikDrinfeld.QM.FakeEllipticCurve.isReduced_pullback_one_of_natCast_ne_zero k E E' φ' hφ' hφ'mul hφ'act ψ' hψ'
      n hnk hψ'φ' hφ'ψ'
  have hred := hKR.1
  have hlft := hKR.2.1
  set e' : Spec (CommRingCat.of k) ⟶ E'.A := (E'.L.one (𝟙 (Spec (CommRingCat.of k)))).1 with he'
  set e'' : Spec (CommRingCat.of k) ⟶ E''.A := (E''.L.one (𝟙 (Spec (CommRingCat.of k)))).1 with he''
  haveI : IsReduced (pullback φ' e') := hred
  haveI : LocallyOfFiniteType (pullback.fst φ' e' ≫ E.f) := hlft

  haveI : IsClosedImmersion e'' :=
    isClosedImmersion_of_comp_eq_id E''.f e'' (E''.L.one (𝟙 _)).2

  have hfst : pullback.fst φ' e' ≫ E.f = pullback.snd φ' e' := by
    rw [← hφ', ← Category.assoc, pullback.condition, Category.assoc]
    change pullback.snd φ' e' ≫ (E'.L.one (𝟙 _)).1 ≫ E'.f = _
    rw [(E'.L.one (𝟙 _)).2, Category.comp_id]

  obtain ⟨φ₀, hφ₀⟩ :=
    CerednikDrinfeld.QM.exists_comp_eq_of_forall_factorsThrough_of_isReduced k (pullback.fst φ' e' ≫ E.f) E''.f e''
      (pullback.fst φ' e' ≫ φ'') (by rw [Category.assoc, hφ'']) (by
        intro z

        have hz : z.1 ≫ pullback.snd φ' e' = 𝟙 _ := by rw [← hfst, ← Category.assoc]; exact z.2
        let Pz : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f :=
          ⟨z.1 ≫ pullback.fst φ' e', by rw [Category.assoc]; exact z.2⟩
        have hPz : mapPt φ' hφ' Pz = E'.L.one _ := by
          apply Subtype.ext
          simp only [mapPt_coe, Pz, Category.assoc, pullback.condition]
          rw [← Category.assoc, hz, Category.id_comp]
        have := hpts Pz hPz
        refine ⟨𝟙 _, ?_⟩
        have h := congrArg Subtype.val this
        simp only [mapPt_coe, Pz, Category.assoc] at h
        simp only [mapPt_coe, Category.id_comp, Category.assoc]
        exact h.symm)

  have hφ₀' : φ₀ = pullback.fst φ' e' ≫ E.f := by
    have : φ₀ ≫ e'' ≫ E''.f = pullback.fst φ' e' ≫ φ'' ≫ E''.f := by rw [← Category.assoc, hφ₀, Category.assoc]
    rw [show e'' ≫ E''.f = 𝟙 _ from (E''.L.one (𝟙 _)).2, Category.comp_id, hφ''] at this
    exact this

  have hP1 : P.1 ≫ φ' = t ≫ e' := by
    have := congrArg Subtype.val hP
    simp only [mapPt_coe] at this
    rw [this, one_comp_val, one_val_congr E'.L _ _ (Category.comp_id t)]
  let lift : T ⟶ pullback φ' e' := pullback.lift P.1 t hP1
  apply Subtype.ext
  simp only [mapPt_coe]
  have hl : lift ≫ pullback.fst φ' e' = P.1 := pullback.lift_fst _ _ _
  calc P.1 ≫ φ'' = lift ≫ pullback.fst φ' e' ≫ φ'' := by rw [← Category.assoc, hl]
    _ = lift ≫ φ₀ ≫ e'' := by rw [hφ₀]
    _ = ((lift ≫ pullback.fst φ' e') ≫ E.f) ≫ e'' := by rw [hφ₀']; simp only [Category.assoc]
    _ = t ≫ e'' := by rw [hl, P.2]
    _ = (E''.L.one t).1 := by rw [one_comp_val, one_val_congr E''.L _ _ (Category.comp_id t)]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_forall_mapPt_eq_one_of_forall_rationalPoint
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_forall_mapPt_eq_one_of_forall_rationalPoint (solution)
