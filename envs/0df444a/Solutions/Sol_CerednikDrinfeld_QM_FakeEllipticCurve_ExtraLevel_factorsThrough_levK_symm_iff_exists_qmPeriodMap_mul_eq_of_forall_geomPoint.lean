-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.factorsThrough_levK_symm_iff_exists_qmPeriodMap_mul_eq_of_forall_geomPoint
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/8f57a2aa-2971-52d6-8642-3bfc98ef7f29

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_etale_and_forall_factorsThrough_iff_of_isUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_factorsThrough_levK_symm_iff_exists_qmPeriodMap_mul_eq_of_forall_geomPoint
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField Pointwise
p2m_open "CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_factorsThrough_levK_symm_iff_exists_qmPeriodMap_mul_eq_of_forall_geomPoint.CerednikDrinfeld CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_factorsThrough_levK_symm_iff_exists_qmPeriodMap_mul_eq_of_forall_geomPoint.CerednikDrinfeld.QM NeronModelInfra~schemeHomOverComp~schemeHomOverComp_coe GoodReductionJacobian"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "QM.FakeEllipticCurve.ExtraLevel QM.FakeEllipticCurve QM.FakeEllipticCurve.ExtraLevel.etale_and_forall_factorsThrough_iff_of_isUnit"
namespace QM
p2m_export "CerednikDrinfeld.QM" "FakeEllipticCurve.sectionAt FakeEllipticCurve.ExtraLevel mapPt_coe pushPt FactorsThrough nsmulPt geomPoint FakeEllipticCurve FakeEllipticCurve.ExtraLevel.etale_and_forall_factorsThrough_iff_of_isUnit"
namespace FibKBody
p2m_open "CerednikDrinfeld.QM CerednikDrinfeld"

variable {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}

theorem comp_pushPt (φ : A ⟶ A) (hφ : φ ≫ f = f) {T T' : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)}
    {t' : T' ⟶ Spec (CommRingCat.of S)} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (R : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (pushPt φ hφ R) = pushPt φ hφ (schemeHomOverComp ψ hψ R) :=
  Subtype.ext (by simp only [schemeHomOverComp_coe, mapPt_coe, Category.assoc])

theorem comp_nsmulPt (L : RelativeGroupLaw S f) {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S))
    (t' : T' ⟶ Spec (CommRingCat.of S)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (n : ℕ) (R : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (nsmulPt L t n R) = nsmulPt L t' n (schemeHomOverComp ψ hψ R) := by
  induction n with
  | zero => exact L.one_natural t t' ψ hψ
  | succ n ih =>
    show schemeHomOverComp ψ hψ (L.mul t (nsmulPt L t n R) R) = L.mul t' (nsmulPt L t' n (schemeHomOverComp ψ hψ R)) _
    rw [L.mul_natural, ih]

theorem hom_nsmulPt (L : RelativeGroupLaw S f) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S))
    (F : SchemeHomOver t f → SchemeHomOver t f) (hF : ∀ P Q, F (L.mul t P Q) = L.mul t (F P) (F Q)) (n : ℕ) (R : SchemeHomOver t f) :
    F (nsmulPt L t n R) = nsmulPt L t n (F R) := by
  letI : Group (SchemeHomOver t f) := L.pointGroup t
  let Fh : SchemeHomOver t f →* SchemeHomOver t f := MonoidHom.mk' F hF
  have hpow : ∀ (k : ℕ) (X : SchemeHomOver t f), nsmulPt L t k X = X ^ k := by
    intro k X
    induction k with
    | zero => exact (pow_zero X).symm
    | succ k ih => rw [show nsmulPt L t (k + 1) X = L.mul t (nsmulPt L t k X) X from rfl, ih, pow_succ]; rfl
  rw [hpow, hpow, show F = ⇑Fh from rfl, map_pow]

theorem nsmulPt_nsmulPt (L : RelativeGroupLaw S f) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S))
    (a' b' : ℕ) (R : SchemeHomOver t f) : nsmulPt L t a' (nsmulPt L t b' R) = nsmulPt L t (b' * a') R := by
  letI : Group (SchemeHomOver t f) := L.pointGroup t
  have hpow : ∀ (k : ℕ) (X : SchemeHomOver t f), nsmulPt L t k X = X ^ k := by
    intro k X
    induction k with
    | zero => exact (pow_zero X).symm
    | succ k ih => rw [show nsmulPt L t (k + 1) X = L.mul t (nsmulPt L t k X) X from rfl, ih, pow_succ]; rfl
  rw [hpow, hpow, hpow, pow_mul]

end CerednikDrinfeld.QM.FibKBody

open CerednikDrinfeld.QM.FibKBody in
theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) {N : ℕ} (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ)
    (E : FakeEllipticCurve Λ N ℂ)

    (latt : Submodule ℤ (Fin 2 → ℂ))
    (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f ≃ ((Fin 2 → ℂ) ⧸ latt.toAddSubgroup))
    (hE1 : ∀ P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f,
      e (E.L.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q) = e P + e Q)
    (hE2 : ∀ (x : ↥Λ) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (v : Fin 2 → ℂ),
      e P = (v : (Fin 2 → ℂ) ⧸ latt.toAddSubgroup) →
      e (pushPt (E.act x) (E.act_over x) P) =
        ((((ι (x : ℍ[ℚ, a, b])).map (algebraMap ℝ ℂ)).mulVec v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ latt.toAddSubgroup))

    (m ℓ : ℕ) (hm : m ≠ 0) (hℓ : ℓ ≠ 0) (hℓm : ℓ ∣ m) (P : E.FullLevel m)
    (τ : UpperHalfPlane) (c : ℂ) (hc : c ≠ 0) (hlatt : c • latt = qmPeriodLattice ι Λ τ)
    (w : ℍ[ℚ, a, b]) (vP : Fin 2 → ℂ) (hvP : e P.P = (vP : (Fin 2 → ℂ) ⧸ latt.toAddSubgroup))
    (hcvP : c • vP = ((m : ℂ)⁻¹) • qmPeriodMap ι τ w)

    (L₀ : Submodule ℤ ℍ[ℚ, a, b]) (t : ℍ[ℚ, a, b])
    (hLT : ∀ y : ℍ[ℚ, a, b], (∃ z ∈ Λ, z * t = y) ↔ ∃ z ∈ Λ, ∃ x ∈ Λ, x ∈ L₀ ∧ (ℓ : ℚ) • z + x * w = y)

    (K : E.ExtraLevel ℓ)
    (hK : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : ℂ →+* k) (Q : SchemeHomOver (geomPoint k sk) E.f),
      FactorsThrough K.levK Q ↔
        ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧
          pushPt (E.act x) (E.act_over x)
            (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk)) = Q)
    (v : Fin 2 → ℂ) :
    FactorsThrough K.levK (e.symm (v : (Fin 2 → ℂ) ⧸ latt.toAddSubgroup)) ↔
      ∃ y ∈ Λ, qmPeriodMap ι τ (y * t) = (c * (ℓ : ℂ)) • v := by
  classical

  set R₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f :=
    nsmulPt E.L (𝟙 (Spec (CommRingCat.of ℂ))) (m / ℓ) P.P with hR₀
  have hψ1 : geomPoint ℂ (RingHom.id ℂ) = 𝟙 (Spec (CommRingCat.of ℂ)) := by
    show Spec.map (CommRingCat.ofHom (RingHom.id ℂ)) = 𝟙 _
    rw [CommRingCat.ofHom_id]; exact Spec.map_id _
  have hact1 : ∀ (x : ↥Λ), pushPt (E.act x) (E.act_over x) (E.L.one (𝟙 (Spec (CommRingCat.of ℂ)))) = E.L.one _ := by
    intro x
    exact hom_nsmulPt E.L (𝟙 _) (fun Q => pushPt (E.act x) (E.act_over x) Q) (fun P' Q => E.act_hom x _ P' Q) 0 (E.L.one _)
  have CLAIM : ∀ Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f,
      FactorsThrough K.levK Q ↔ ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧ pushPt (E.act x) (E.act_over x) R₀ = Q := by
    intro Q
    constructor
    · intro hQ

      have h : geomPoint ℂ (RingHom.id ℂ) ≫ 𝟙 (Spec (CommRingCat.of ℂ)) = geomPoint ℂ (RingHom.id ℂ) := Category.comp_id _
      obtain ⟨Q₀, hQ₀⟩ := hQ
      have hQ' : FactorsThrough K.levK (schemeHomOverComp (geomPoint ℂ (RingHom.id ℂ)) h Q) :=
        ⟨geomPoint ℂ (RingHom.id ℂ) ≫ Q₀, by rw [Category.assoc, hQ₀, schemeHomOverComp_coe]⟩
      obtain ⟨x, hx, heq⟩ := (hK ℂ (RingHom.id ℂ) _).1 hQ'
      refine ⟨x, hx, ?_⟩

      have hsec : FakeEllipticCurve.sectionAt P.P ℂ (RingHom.id ℂ) = schemeHomOverComp (geomPoint ℂ (RingHom.id ℂ)) h P.P := rfl
      rw [hsec, ← comp_nsmulPt, ← comp_pushPt] at heq
      have := congrArg Subtype.val heq
      rw [schemeHomOverComp_coe, schemeHomOverComp_coe, hψ1, Category.id_comp, Category.id_comp] at this
      exact Subtype.ext this
    · rintro ⟨x, hx, rfl⟩
      refine ((CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.etale_and_forall_factorsThrough_iff_of_isUnit E ℓ
        (by exact_mod_cast (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hℓ) : IsUnit ((ℓ : ℂ)))) K).2 _ _).2 ⟨?_, ?_⟩
      ·
        rw [← hom_nsmulPt E.L _ (fun Q => pushPt (E.act x) (E.act_over x) Q) (fun P' Q => E.act_hom x _ P' Q), hR₀,
          nsmulPt_nsmulPt, Nat.div_mul_cancel hℓm, P.torsion, hact1]
      · intro k _ _ sk τ' hτ'
        rw [comp_pushPt, hR₀, comp_nsmulPt]
        have hsec : schemeHomOverComp τ' hτ' P.P = FakeEllipticCurve.sectionAt P.P k sk := by
          apply Subtype.ext
          show τ' ≫ P.P.1 = geomPoint k sk ≫ P.P.1
          rw [← hτ', Category.comp_id]
        rw [hsec]
        exact (hK k sk _).2 ⟨x, hx, rfl⟩

  have he_one : e (E.L.one (𝟙 _)) = 0 := by
    have h := hE1 (E.L.one (𝟙 _)) (E.L.one (𝟙 _))
    rw [E.L.one_mul] at h
    exact left_eq_add.mp h
  have he_nsmul : ∀ (n : ℕ) (Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f), e (nsmulPt E.L (𝟙 _) n Q) = n • e Q := by
    intro n Q
    induction n with
    | zero => rw [zero_smul]; exact he_one
    | succ n ih => rw [show nsmulPt E.L (𝟙 _) (n + 1) Q = E.L.mul _ (nsmulPt E.L (𝟙 _) n Q) Q from rfl, hE1, ih, succ_nsmul]
  have heR₀ : e R₀ = (((m / ℓ : ℕ) • vP : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ latt.toAddSubgroup) := by
    rw [hR₀, he_nsmul, hvP]; rfl
  have hexR : ∀ x : ↥Λ, e (pushPt (E.act x) (E.act_over x) R₀) =
      ((((ι (x : ℍ[ℚ, a, b])).map (algebraMap ℝ ℂ)).mulVec ((m / ℓ : ℕ) • vP) : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ latt.toAddSubgroup) :=
    fun x => hE2 x R₀ _ heR₀

  have hmul : ∀ x y : ℍ[ℚ, a, b], qmPeriodMap ι τ (x * y) = ((ι x).map (algebraMap ℝ ℂ)).mulVec (qmPeriodMap ι τ y) := by
    intro x y
    rw [qmPeriodMap_apply, qmPeriodMap_apply, map_mul, Matrix.map_mul, Matrix.mulVec_mulVec]
  have hsmulℓ : ∀ z : ℍ[ℚ, a, b], qmPeriodMap ι τ ((ℓ : ℚ) • z) = (ℓ : ℂ) • qmPeriodMap ι τ z := by
    intro z
    rw [show (ℓ : ℚ) • z = (ℓ : ℕ) • z from (Nat.cast_smul_eq_nsmul ℚ ℓ z), map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ]

  have hmC : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hℓC : (ℓ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hℓ
  have hdiv : ((m / ℓ : ℕ) : ℂ) * (ℓ : ℂ) = m := by exact_mod_cast Nat.div_mul_cancel hℓm

  have hlat : ∀ u : Fin 2 → ℂ, (∃ z ∈ Λ, qmPeriodMap ι τ z = u) ↔ ∃ l ∈ latt, c • l = u := by
    intro u
    rw [← mem_qmPeriodLattice_iff, ← hlatt, Submodule.mem_smul_pointwise_iff_exists]
  have hw' : qmPeriodMap ι τ w = (m : ℂ) • (c • vP) := by
    rw [hcvP, smul_smul, mul_inv_cancel₀ hmC, one_smul]
  have hkey : ∀ x : ℍ[ℚ, a, b],
      (c * (ℓ : ℂ)) • ((ι x).map (algebraMap ℝ ℂ)).mulVec ((m / ℓ : ℕ) • vP) = qmPeriodMap ι τ (x * w) := by
    intro x
    rw [← Nat.cast_smul_eq_nsmul ℂ (m / ℓ) vP, hmul, hw']
    simp only [Matrix.mulVec_smul, smul_smul]
    rw [show c * (ℓ : ℂ) * ((m / ℓ : ℕ) : ℂ) = (m : ℂ) * c by rw [mul_assoc, mul_comm (ℓ : ℂ), hdiv, mul_comm]]

  rw [CLAIM]
  constructor
  · rintro ⟨x, hx, heq⟩

    have h1 : e (e.symm (v : (Fin 2 → ℂ) ⧸ latt.toAddSubgroup)) = e (pushPt (E.act x) (E.act_over x) R₀) := by rw [heq]
    rw [Equiv.apply_symm_apply, hexR] at h1

    obtain ⟨l, hl, hlv⟩ := (QuotientAddGroup.mk'_eq_mk' latt.toAddSubgroup).1 h1.symm

    obtain ⟨z, hz, hzl⟩ := (hlat (c • l)).2 ⟨l, hl, rfl⟩

    have hsum : (c * (ℓ : ℂ)) • v = qmPeriodMap ι τ ((ℓ : ℚ) • z + (x : ℍ[ℚ, a, b]) * w) := by
      rw [← hlv, smul_add, hkey, map_add, hsmulℓ, hzl, mul_comm c, ← smul_smul, add_comm]
    obtain ⟨y, hy, hyt⟩ := (hLT _).2 ⟨z, hz, x, x.2, hx, rfl⟩
    exact ⟨y, hy, by rw [hyt, ← hsum]⟩
  · rintro ⟨y, hy, hyt⟩
    obtain ⟨z, hz, x, hxΛ, hx, hsum⟩ := (hLT (y * t)).1 ⟨y, hy, rfl⟩
    refine ⟨⟨x, hxΛ⟩, hx, ?_⟩

    obtain ⟨l, hl, hzl⟩ := (hlat (qmPeriodMap ι τ z)).1 ⟨z, hz, rfl⟩

    have h2 : (c * (ℓ : ℂ)) • v = (c * (ℓ : ℂ)) • (((ι x).map (algebraMap ℝ ℂ)).mulVec ((m / ℓ : ℕ) • vP) + l) := by
      rw [smul_add, hkey, ← hyt, ← hsum, map_add, hsmulℓ, ← hzl, smul_smul, mul_comm (ℓ : ℂ) c, add_comm]
    have hcl : c * (ℓ : ℂ) ≠ 0 := mul_ne_zero hc hℓC
    have hv : v = ((ι x).map (algebraMap ℝ ℂ)).mulVec ((m / ℓ : ℕ) • vP) + l := smul_right_injective _ hcl h2
    apply e.injective
    rw [Equiv.apply_symm_apply, hexR, hv]
    exact (QuotientAddGroup.mk'_eq_mk' latt.toAddSubgroup).2 ⟨l, hl, rfl⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_factorsThrough_levK_symm_iff_exists_qmPeriodMap_mul_eq_of_forall_geomPoint
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_factorsThrough_levK_symm_iff_exists_qmPeriodMap_mul_eq_of_forall_geomPoint (solution)
