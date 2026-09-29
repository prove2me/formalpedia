-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormalODModule.exists_maximalIdeal_eq_map_sup_span_singleton_sup_sq_of_isProrepresentedBy_deformations_of_not_and
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/8da7c1f2-bd8b-5387-9d70-aa59a3ccac60

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_injective_deformations_dualNumber_fin_one_of_not_and
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_injective_ringHom_dualNumber_of_exists_injective_deformations_dualNumber
import Theorems.Thm_IsLocalRing_maximalIdeal_eq_map_sup_span_sup_sq_of_forall_ringHom_dualNumber_eqOn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_maximalIdeal_eq_map_sup_span_singleton_sup_sq_of_isProrepresentedBy_deformations_of_not_and
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra"
p2m_attr_erase "simp" "MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq Deformation.DieudonneDatum.mk.sizeOf_spec Deformation.HondaSystem.mk.injEq Deformation.DieudonneDatum.mk.injEq Deformation.HondaSystem.mk.sizeOf_spec CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul MvPowerSeries.kw_coeff_pderiv FormalGroup.nthSeries_zero FormalGroup.evalNSMul_zero"

set_option autoImplicit false

open IsLocalRing TrivSqZeroExt

namespace DDF2

section Scale
variable {k : Type} [Field k]

noncomputable def scale (c : k) : DualNumber k →+* DualNumber k :=
  (TrivSqZeroExt.map (c • (LinearMap.id : k →ₗ[k] k))).toRingHom

@[scoped simp] theorem fst_scale (c : k) (x : DualNumber k) : fst (scale c x) = fst x := by
  simp [scale, TrivSqZeroExt.fst_map]

@[scoped simp] theorem snd_scale (c : k) (x : DualNumber k) : snd (scale c x) = c * snd x := by
  simp [scale, TrivSqZeroExt.snd_map]

theorem fstHom_comp_scale (c : k) :
    (TrivSqZeroExt.fstHom k k k).toRingHom.comp (scale c) = (TrivSqZeroExt.fstHom k k k).toRingHom :=
  RingHom.ext fun x => by simp

theorem scale_inl (c : k) (a : k) : scale c (inl a) = inl a := by
  apply TrivSqZeroExt.ext <;> simp

end Scale

section Compat
variable {Onr : Type} [CommRing Onr] [IsLocalRing Onr]
variable {R : Type} [CommRing R] [Algebra Onr R]

abbrev Compat (resR : R →+* ResidueField Onr) (χ : R →+* DualNumber (ResidueField Onr)) : Prop :=
  (TrivSqZeroExt.fstHom (ResidueField Onr) (ResidueField Onr) (ResidueField Onr)).toRingHom.comp χ = resR ∧
    χ.comp (algebraMap Onr R) =
      (algebraMap (ResidueField Onr) (DualNumber (ResidueField Onr))).comp (IsLocalRing.residue Onr)

theorem algebraMap_dualNumber_apply (a : ResidueField Onr) :
    algebraMap (ResidueField Onr) (DualNumber (ResidueField Onr)) a = inl a :=
  TrivSqZeroExt.algebraMap_eq_inl' (S := ResidueField Onr) (R := ResidueField Onr) (M := ResidueField Onr) a

theorem Compat.fst_apply {resR : R →+* ResidueField Onr} {χ : R →+* DualNumber (ResidueField Onr)}
    (h : Compat resR χ) (r : R) : fst (χ r) = resR r := by
  have := congrArg (fun f : R →+* ResidueField Onr => f r) h.1
  simpa using this

theorem Compat.apply_algebraMap {resR : R →+* ResidueField Onr} {χ : R →+* DualNumber (ResidueField Onr)}
    (h : Compat resR χ) (o : Onr) : χ (algebraMap Onr R o) = inl (IsLocalRing.residue Onr o) := by
  have := congrArg (fun f : Onr →+* DualNumber (ResidueField Onr) => f o) h.2
  simpa [algebraMap_dualNumber_apply] using this

theorem Compat.scale_comp {resR : R →+* ResidueField Onr} {χ : R →+* DualNumber (ResidueField Onr)}
    (h : Compat resR χ) (c : ResidueField Onr) : Compat resR ((scale c).comp χ) := by
  refine ⟨?_, ?_⟩
  · rw [← RingHom.comp_assoc, fstHom_comp_scale]; exact h.1
  · rw [RingHom.comp_assoc, h.2]
    ext o
    · simp [algebraMap_dualNumber_apply, scale_inl]
    · simp [algebraMap_dualNumber_apply, scale_inl]

theorem compat_trivial (resR : R →+* ResidueField Onr) (hresR : resR.comp (algebraMap Onr R) = IsLocalRing.residue Onr) :
    Compat resR ((algebraMap (ResidueField Onr) (DualNumber (ResidueField Onr))).comp resR) := by
  refine ⟨?_, ?_⟩
  · ext r; simp [algebraMap_dualNumber_apply]
  · rw [RingHom.comp_assoc, hresR]

end Compat

end DDF2
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_maximalIdeal_eq_map_sup_span_singleton_sup_sq_of_isProrepresentedBy_deformations_of_not_and.DDF2"

open DDF2 in
open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in
theorem solution
    {q : ℕ} [Fact q.Prime]
    (Onr : Type) [CommRing Onr] [IsDomain Onr] [IsDiscreteValuationRing Onr] [CharZero Onr] [Algebra ℤ_[q] Onr]
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}) Onr)
    (hOnr_max : (Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}).IsMaximal)
    [IsAlgClosed (IsLocalRing.ResidueField Onr)]
    (ι : Zp2 q →+* Onr) (X₀ : SpecialFormalODModule q ((IsLocalRing.residue Onr).comp ι))
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra Onr R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (resR : R →+* IsLocalRing.ResidueField Onr) (hresR : resR.comp (algebraMap Onr R) = IsLocalRing.residue Onr)
    (Xu : FormalODModule q R) (wu : (Xu.map resR).Hom X₀.toFormalODModule) (hwu : wu.IsIso)
    (hPRO : (∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra Onr A]
            (resA : A →+* IsLocalRing.ResidueField Onr), Function.Surjective resA →
            resA.comp (algebraMap Onr A) = IsLocalRing.residue Onr →
          ∀ (X : FormalODModule q A), X.IsSpecial ((algebraMap Onr A).comp ι) → X.HasHeight 4 →
          ∀ (w : (X.map resA).Hom X₀.toFormalODModule), w.IsIso →
            ∃! χ : R →ₐ[Onr] A, resA.comp χ.toRingHom = resR ∧
              ∃ v : (Xu.map χ.toRingHom).Hom X, v.IsIso ∧
                (w.comp (v.map resA)).toSeries = wu.toSeries))
    (hsmooth : ¬ ((∀ m ∈ X₀.toFormalODModule.lieZero ((IsLocalRing.residue Onr).comp ι), Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0) ∧
        (∀ m ∈ X₀.toFormalODModule.lieOne ((IsLocalRing.residue Onr).comp ι), Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0))) :
    ∃ t ∈ IsLocalRing.maximalIdeal R,
      IsLocalRing.maximalIdeal R = (IsLocalRing.maximalIdeal Onr).map (algebraMap Onr R) ⊔ Ideal.span {t} ⊔ (IsLocalRing.maximalIdeal R) ^ 2 := by
  classical

  have hqk : ((q : ℕ) : IsLocalRing.ResidueField Onr) = 0 := by
    have hmem : ((q : ℕ) : Onr) ∈ maximalIdeal Onr := by
      rw [← IsLocalRing.eq_maximalIdeal hOnr_max, ← map_natCast (algebraMap ℤ_[q] Onr) q]
      exact Ideal.subset_span rfl
    have := (IsLocalRing.residue_eq_zero_iff _).mpr hmem
    rwa [map_natCast] at this
  haveI : CharP (IsLocalRing.ResidueField Onr) q := (CharP.charP_iff_prime_eq_zero (Fact.out : q.Prime)).mpr hqk

  obtain ⟨e, h1, h2, h3, h4⟩ :=
    CerednikDrinfeld.SpecialFormalODModule.exists_injective_deformations_dualNumber_fin_one_of_not_and (j₀ := (IsLocalRing.residue Onr).comp ι) X₀ hsmooth
  obtain ⟨e', hinj, hhom, -⟩ :=
    CerednikDrinfeld.SpecialFormalODModule.exists_injective_ringHom_dualNumber_of_exists_injective_deformations_dualNumber
      Onr hOnr_complete hOnr_max ι X₀ R resR hresR Xu wu hwu hPRO (r := 1) ⟨e, h1, h2, h3, h4⟩

  have hsurj : Function.Surjective resR := by
    intro y; obtain ⟨o, rfl⟩ := IsLocalRing.residue_surjective y
    exact ⟨algebraMap Onr R o, by rw [← RingHom.comp_apply, hresR]⟩
  have hker : RingHom.ker resR = maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective resR hsurj)
  set χ₀ : R →+* DualNumber (IsLocalRing.ResidueField Onr) := (algebraMap (IsLocalRing.ResidueField Onr) (DualNumber (IsLocalRing.ResidueField Onr))).comp resR with hχ₀
  have hχ₀c : Compat resR χ₀ := compat_trivial resR hresR
  by_cases hall : ∀ χ : R →+* DualNumber (IsLocalRing.ResidueField Onr), Compat resR χ → χ = χ₀
  · refine ⟨0, Ideal.zero_mem _, ?_⟩
    exact IsLocalRing.maximalIdeal_eq_map_sup_span_sup_sq_of_forall_ringHom_dualNumber_eqOn Onr R resR hresR {0}
      (by simp) (fun χ χ' hχ hχ' _ => (hall χ hχ).trans (hall χ' hχ').symm)
  · push Not at hall
    obtain ⟨χ₁, hχ₁c, hne⟩ := hall

    have hex : ∃ r, snd (χ₁ r) ≠ 0 := by
      by_contra h
      push Not at h
      apply hne
      ext r
      · rw [hχ₁c.fst_apply, hχ₀c.fst_apply]
      · rw [h r, hχ₀]; simp [algebraMap_dualNumber_apply]
    obtain ⟨r, hr⟩ := hex
    obtain ⟨o, ho⟩ := IsLocalRing.residue_surjective (resR r)
    set t : R := r - algebraMap Onr R o with ht
    have ht_mem : t ∈ maximalIdeal R := by
      rw [← hker, RingHom.mem_ker, ht, map_sub, ← RingHom.comp_apply, hresR, ho, sub_self]
    have hsndt : snd (χ₁ t) = snd (χ₁ r) := by
      rw [ht, map_sub, snd_sub, hχ₁c.apply_algebraMap, snd_inl, sub_zero]

    have he0 : e' χ₀ = 0 := by
      have h := hhom 0 (scale 0) (fstHom_comp_scale 0) (fun x => snd_scale 0 x) χ₁ hχ₁c
      have hsc : (scale (0 : IsLocalRing.ResidueField Onr)).comp χ₁ = χ₀ := by
        ext x
        · simp [hχ₁c.fst_apply, hχ₀, algebraMap_dualNumber_apply]
        · simp [hχ₀, algebraMap_dualNumber_apply]
      rwa [hsc, zero_smul] at h
    have ha : e' χ₁ 0 ≠ 0 := by
      intro h0
      apply hne
      apply hinj χ₁ χ₀ hχ₁c hχ₀c
      rw [he0]
      funext i
      fin_cases i
      simpa using h0

    have key : ∀ χ, Compat resR χ → χ = (scale (e' χ 0 / e' χ₁ 0)).comp χ₁ := by
      intro χ hχc
      apply hinj χ _ hχc (hχ₁c.scale_comp _)
      rw [hhom _ (scale _) (fstHom_comp_scale _) (fun x => snd_scale _ x) χ₁ hχ₁c]
      funext i
      fin_cases i
      simp [div_mul_cancel₀ _ ha]
    refine ⟨t, ht_mem, ?_⟩
    refine IsLocalRing.maximalIdeal_eq_map_sup_span_sup_sq_of_forall_ringHom_dualNumber_eqOn Onr R resR hresR {t}
      (by simpa using ht_mem) ?_
    intro χ χ' hχ hχ' hs
    have hct := hs t (by simp)
    rw [key χ hχ, key χ' hχ'] at hct ⊢
    simp only [RingHom.comp_apply] at hct
    have h2 := congrArg snd hct
    rw [snd_scale, snd_scale, hsndt] at h2
    rw [mul_right_cancel₀ hr h2]

#print axioms solution

end S_CerednikDrinfeld_SpecialFormalODModule_exists_maximalIdeal_eq_map_sup_span_singleton_sup_sq_of_isProrepresentedBy_deformations_of_not_and
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_maximalIdeal_eq_map_sup_span_singleton_sup_sq_of_isProrepresentedBy_deformations_of_not_and (solution)
