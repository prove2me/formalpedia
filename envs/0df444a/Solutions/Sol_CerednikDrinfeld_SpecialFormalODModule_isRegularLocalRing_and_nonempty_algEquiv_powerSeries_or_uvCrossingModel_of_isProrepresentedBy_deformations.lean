-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormalODModule.isRegularLocalRing_and_nonempty_algEquiv_powerSeries_or_uvCrossingModel_of_isProrepresentedBy_deformations
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/adda97e9-121d-5922-bba8-e0a1ed363211

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_maximalIdeal_eq_map_sup_span_singleton_sup_sq_of_isProrepresentedBy_deformations_of_not_and
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_mul_eq_algebraMap_and_maximalIdeal_eq_map_sup_span_pair_sup_sq_of_isProrepresentedBy_deformations
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_two_le_ringKrullDim_of_isProrepresentedBy_deformations
import Theorems.Thm_IsLocalRing_nonempty_algEquiv_powerSeries_of_maximalIdeal_eq_sup_span_singleton_sup_sq_of_two_le_ringKrullDim
import Theorems.Thm_IsLocalRing_nonempty_algEquiv_uvCrossingModel_of_mul_eq_of_maximalIdeal_eq_sup_span_pair_sup_sq_of_two_le_ringKrullDim
import Theorems.Thm_IsRegularLocalRing_mvPowerSeries_fin
import Theorems.Thm_IsRegularLocalRing_quotient_span_singleton_of_notMem_sq_of_forall_minimalPrimes_notMem
import Theorems.Thm_ModularCurve_UVCrossingModel_const_mem_nonZeroDivisors
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormalODModule_isRegularLocalRing_and_nonempty_algEquiv_powerSeries_or_uvCrossingModel_of_isProrepresentedBy_deformations
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra MvFormalGroup.CartierModule.instAddCommGroup MvFormalGroup.CartierModule.instNeg MvFormalGroup.CartierModule.instAdd MvFormalGroup.CartierModule.instZero MvFormalGroup.WittLaw.instTendstoCofiniteProdMk MvFormalGroup.CartierModule.instModuleWittVector MvFormalGroup.instIsCommMapRingHom MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq Deformation.DieudonneDatum.mk.sizeOf_spec Deformation.HondaSystem.mk.injEq Deformation.DieudonneDatum.mk.injEq Deformation.HondaSystem.mk.sizeOf_spec CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul MvPowerSeries.kw_coeff_pderiv FormalGroup.nthSeries_zero FormalGroup.evalNSMul_zero MvFormalGroup.CartierModule.toPowerSeries_sub MvFormalGroup.WittLaw.verFam_zero MvFormalGroup.WittLaw.verFam_succ MvFormalGroup.CartierModule.toPowerSeries_frobenius"
p2m_attr_erase "simp" "MvFormalGroup.CartierModule.toPowerSeries_verschiebung MvFormalGroup.WittLaw.blk_apply MvFormalGroup.WittLaw.weight_apply MvFormalGroup.CartierModule.toPowerSeries_map MvFormalGroup.CartierModule.toPowerSeries_precompFun MvFormalGroup.CartierModule.toPowerSeries_mapFun MvFormalGroup.CartierModule.mk.injEq MvFormalGroup.WittLaw.pairFam_apply MvFormalGroup.CartierModule.endAct_apply MvFormalGroup.WittLaw.frobFam_apply MvFormalGroup.CartierModule.toPowerSeries_zero MvFormalGroup.CartierModule.tangent_apply MvFormalGroup.CartierModule.toPowerSeries_precomp MvFormalGroup.CartierModule.Examples.toPowerSeries_addLinear MvFormalGroup.CartierModule.toPowerSeries_add MvFormalGroup.CartierModule.toPowerSeries_neg MvFormalGroup.CartierModule.mk.sizeOf_spec MvFormalGroup.CartierModule.inBlk_apply MvFormalGroup.WittLaw.teichFam_apply MvFormalGroup.CartierModule.toPowerSeries_homothety MvFormalGroup.WittLaw.verPoly_succ MvFormalGroup.WittLaw.xVec_coeff MvFormalGroup.WittLaw.cVec_coeff MvFormalGroup.WittLaw.cVec_mul MvFormalGroup.WittLaw.mulFam_apply MvFormalGroup.CartierModule.mapLinear_apply MvFormalGroup.WittLaw.cVec_add MvFormalGroup.WittLaw.cVec_zero MvFormalGroup.WittLaw.verPoly_zero MvFormalGroup.CartierModule.toPowerSeries_wittSMul MvFormalGroup.CartierModule.toPowerSeries_smul_witt MvFormalGroup.WittLaw.cVec_one MvFormalGroup.CartierModule.toPowerSeries_verschiebungInt MvFormalGroup.WittLaw.xTaut_coeff MvFormalGroup.WittLaw.frobPolyFam_apply MvFormalGroup.CartierModule.toPowerSeries_baseChangeEqFun MvFormalGroup.toPowerSeries_map_ringHom MvFormalGroup.CartierModule.toPowerSeries_baseChangeEq MvPowerSeries.blockPermEmbed_apply MvFormalGroup.BigWittLaw.projPoly_zero"
p2m_attr_erase "simp" "MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt"

set_option autoImplicit false

open IsLocalRing

namespace DDReduce7d

section Models

variable {q : ℕ} [Fact q.Prime]
variable (Onr : Type) [CommRing Onr] [IsDomain Onr] [IsDiscreteValuationRing Onr] [Algebra ℤ_[q] Onr]

theorem maximalIdeal_eq_span (hOnr_max : (Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}).IsMaximal) :
    maximalIdeal Onr = Ideal.span {((q : ℕ) : Onr)} := by
  rw [← IsLocalRing.eq_maximalIdeal hOnr_max, map_natCast]

theorem natCast_ne_zero (hOnr_max : (Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}).IsMaximal) :
    ((q : ℕ) : Onr) ≠ 0 := by
  intro h
  apply IsDiscreteValuationRing.not_a_field' (R := Onr)
  rw [maximalIdeal_eq_span Onr hOnr_max, h, Ideal.span_singleton_eq_bot]

theorem natCast_mem_maximalIdeal (hOnr_max : (Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}).IsMaximal) :
    ((q : ℕ) : Onr) ∈ maximalIdeal Onr := by
  rw [maximalIdeal_eq_span Onr hOnr_max]; exact Ideal.subset_span rfl

theorem natCast_not_mem_sq (hOnr_max : (Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}).IsMaximal) :
    ((q : ℕ) : Onr) ∉ maximalIdeal Onr ^ 2 := by
  intro h
  rw [maximalIdeal_eq_span Onr hOnr_max, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
  obtain ⟨r, hr⟩ := h
  have hq := natCast_ne_zero Onr hOnr_max
  have h1 : ((q : ℕ) : Onr) * (1 - (q : Onr) * r) = 0 := by
    rw [mul_sub, mul_one, ← mul_assoc, ← sq, ← hr, sub_self]
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact hq h2
  · have hu : IsUnit ((q : ℕ) : Onr) := IsUnit.of_mul_eq_one r (by rwa [sub_eq_zero, eq_comm] at h2)
    exact (IsLocalRing.mem_maximalIdeal _).mp (natCast_mem_maximalIdeal Onr hOnr_max) hu

theorem isRegularLocalRing_powerSeries : IsRegularLocalRing (PowerSeries Onr) := by
  haveI : IsRegularLocalRing (MvPowerSeries (Fin 1) Onr) := IsRegularLocalRing.mvPowerSeries_fin Onr 1
  exact IsRegularLocalRing.of_ringEquiv
    (MvPowerSeries.renameEquiv Onr finOneEquiv).toRingEquiv

theorem natCast_ne_zero_powerSeries (hOnr_max : (Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}).IsMaximal) :
    ((q : ℕ) : PowerSeries Onr) ≠ 0 := by
  intro h
  apply natCast_ne_zero Onr hOnr_max
  have h1 : PowerSeries.constantCoeff (R := Onr) ((q : ℕ) : PowerSeries Onr) = 0 := by rw [h, map_zero]
  rwa [map_natCast] at h1

theorem crossing_mem_maximalIdeal (hOnr_max : (Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}).IsMaximal) :
    (MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C ((q : ℕ) : Onr) : MvPowerSeries (Fin 2) Onr) ∈
      maximalIdeal (MvPowerSeries (Fin 2) Onr) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff, map_sub, map_mul,
    MvPowerSeries.constantCoeff_X, zero_mul, MvPowerSeries.constantCoeff_C, zero_sub, IsUnit.neg_iff]
  exact (IsLocalRing.mem_maximalIdeal _).mp (natCast_mem_maximalIdeal Onr hOnr_max)

theorem crossing_not_mem_sq (hOnr_max : (Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}).IsMaximal) :
    (MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C ((q : ℕ) : Onr) : MvPowerSeries (Fin 2) Onr) ∉
      maximalIdeal (MvPowerSeries (Fin 2) Onr) ^ 2 := by
  intro h

  set cc : MvPowerSeries (Fin 2) Onr →+* Onr := MvPowerSeries.constantCoeff with hcc
  have hle : Ideal.map cc (maximalIdeal (MvPowerSeries (Fin 2) Onr)) ≤ maximalIdeal Onr := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff] at hx
    exact hx
  have h2 : cc (MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C ((q : ℕ) : Onr)) ∈ maximalIdeal Onr ^ 2 := by
    have h3 := Ideal.mem_map_of_mem cc h
    rw [Ideal.map_pow] at h3
    exact Ideal.pow_right_mono hle 2 h3
  rw [hcc, map_sub, map_mul, MvPowerSeries.constantCoeff_X, zero_mul, MvPowerSeries.constantCoeff_C, zero_sub,
    neg_mem_iff] at h2
  exact natCast_not_mem_sq Onr hOnr_max h2

theorem isRegularLocalRing_uvCrossingModel (hOnr_max : (Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}).IsMaximal) :
    IsRegularLocalRing (ModularCurve.UVCrossingModel Onr ((q : ℕ) : Onr)) := by
  haveI : IsRegularLocalRing (MvPowerSeries (Fin 2) Onr) := IsRegularLocalRing.mvPowerSeries_fin Onr 2
  have hmem := crossing_mem_maximalIdeal Onr hOnr_max
  have hne : ModularCurve.uvCrossingIdeal Onr ((q : ℕ) : Onr) ≠ ⊤ := by
    intro htop
    have : (MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C ((q : ℕ) : Onr) : MvPowerSeries (Fin 2) Onr) ∈
        maximalIdeal (MvPowerSeries (Fin 2) Onr) := hmem
    apply (maximalIdeal.isMaximal (MvPowerSeries (Fin 2) Onr)).ne_top
    rw [eq_top_iff, ← htop, Ideal.span_le, Set.singleton_subset_iff]
    exact this
  haveI : Nontrivial (ModularCurve.UVCrossingModel Onr ((q : ℕ) : Onr)) := Ideal.Quotient.nontrivial_iff.mpr hne
  haveI : IsLocalRing (ModularCurve.UVCrossingModel Onr ((q : ℕ) : Onr)) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  refine (IsRegularLocalRing.quotient_span_singleton_of_notMem_sq_of_forall_minimalPrimes_notMem
    (MvPowerSeries (Fin 2) Onr) hmem (crossing_not_mem_sq Onr hOnr_max) ?_).1
  intro p hp
  have hp' : p = ⊥ := by
    have : p ∈ (⊥ : Ideal (MvPowerSeries (Fin 2) Onr)).minimalPrimes := hp
    rw [Ideal.minimalPrimes_eq_subsingleton_self] at this
    exact this
  rw [hp', Ideal.mem_bot, sub_eq_zero]
  intro h
  have h1 := congrArg (MvPowerSeries.constantCoeff (σ := Fin 2) (R := Onr)) h
  rw [map_mul, MvPowerSeries.constantCoeff_X, zero_mul, MvPowerSeries.constantCoeff_C] at h1
  exact natCast_ne_zero Onr hOnr_max h1.symm

theorem natCast_ne_zero_uvCrossingModel (hOnr_max : (Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}).IsMaximal) :
    ((q : ℕ) : ModularCurve.UVCrossingModel Onr ((q : ℕ) : Onr)) ≠ 0 := by
  haveI := isRegularLocalRing_uvCrossingModel Onr hOnr_max
  have hq : ((q : ℕ) : Onr) ∈ nonZeroDivisors Onr := mem_nonZeroDivisors_of_ne_zero (natCast_ne_zero Onr hOnr_max)
  have h := ModularCurve.UVCrossingModel.const_mem_nonZeroDivisors hq
  have hc : ModularCurve.UVCrossingModel.const ((q : ℕ) : Onr) ((q : ℕ) : Onr) =
      ((q : ℕ) : ModularCurve.UVCrossingModel Onr ((q : ℕ) : Onr)) := by
    show Ideal.Quotient.mk _ (MvPowerSeries.C ((q : ℕ) : Onr)) = _
    rw [map_natCast, map_natCast]
  rw [hc] at h
  exact nonZeroDivisors.ne_zero h

end Models

section Frame

variable {q : ℕ} [Fact q.Prime]
variable (Onr : Type) [CommRing Onr] [IsDomain Onr] [IsDiscreteValuationRing Onr] [Algebra ℤ_[q] Onr]

theorem isAdicComplete_maximalIdeal
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}) Onr)
    (hOnr_max : (Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}).IsMaximal) :
    IsAdicComplete (maximalIdeal Onr) Onr := by
  rwa [IsLocalRing.eq_maximalIdeal hOnr_max] at hOnr_complete

theorem irreducible_natCast (hOnr_max : (Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}).IsMaximal) :
    Irreducible ((q : ℕ) : Onr) :=
  (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr (maximalIdeal_eq_span Onr hOnr_max)

theorem residue_comp_algebraMap_surjective
    (R : Type) [CommRing R] [IsLocalRing R] [Algebra Onr R]
    (resR : R →+* ResidueField Onr) (hresR : resR.comp (algebraMap Onr R) = IsLocalRing.residue Onr) :
    Function.Surjective ((IsLocalRing.residue R).comp (algebraMap Onr R)) := by
  have hsurj : Function.Surjective resR := by
    intro x
    obtain ⟨o, rfl⟩ := IsLocalRing.residue_surjective x
    exact ⟨algebraMap Onr R o, by rw [← RingHom.comp_apply, hresR]⟩
  have hker : RingHom.ker resR = maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective resR hsurj)
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨o, ho⟩ := IsLocalRing.residue_surjective (resR x)
  refine ⟨o, ?_⟩
  rw [RingHom.comp_apply]
  change IsLocalRing.residue R (algebraMap Onr R o) = IsLocalRing.residue R x
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, ← hker, RingHom.mem_ker, map_sub, sub_eq_zero,
    ← RingHom.comp_apply, hresR, ho]

end Frame

end DDReduce7d

open DDReduce7d in
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
                (w.comp (v.map resA)).toSeries = wu.toSeries)) :
    IsRegularLocalRing R ∧ ((q : ℕ) : R) ≠ 0 ∧
      (Nonempty (R ≃ₐ[Onr] PowerSeries Onr) ∨
        Nonempty (R ≃ₐ[Onr] ModularCurve.UVCrossingModel Onr ((q : ℕ) : Onr))) := by
  classical
  haveI : IsAdicComplete (maximalIdeal Onr) Onr := isAdicComplete_maximalIdeal Onr hOnr_complete hOnr_max
  have hirr : Irreducible ((q : ℕ) : Onr) := irreducible_natCast Onr hOnr_max
  have hres : Function.Surjective ((IsLocalRing.residue R).comp (algebraMap Onr R)) :=
    residue_comp_algebraMap_surjective Onr R resR hresR
  have hdim : 2 ≤ ringKrullDim R :=
    CerednikDrinfeld.SpecialFormalODModule.two_le_ringKrullDim_of_isProrepresentedBy_deformations
      Onr hOnr_complete hOnr_max ι X₀ R resR hresR Xu wu hwu hPRO
  by_cases hnode : (∀ m ∈ X₀.toFormalODModule.lieZero ((IsLocalRing.residue Onr).comp ι), Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0) ∧
      (∀ m ∈ X₀.toFormalODModule.lieOne ((IsLocalRing.residue Onr).comp ι), Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0)
  ·
    obtain ⟨u, -, v, -, huv, huv'⟩ :=
      CerednikDrinfeld.SpecialFormalODModule.exists_mul_eq_algebraMap_and_maximalIdeal_eq_map_sup_span_pair_sup_sq_of_isProrepresentedBy_deformations
        Onr hOnr_complete hOnr_max ι X₀ R resR hresR Xu wu hwu hPRO hnode.1 hnode.2
    obtain ⟨e⟩ :=
      IsLocalRing.nonempty_algEquiv_uvCrossingModel_of_mul_eq_of_maximalIdeal_eq_sup_span_pair_sup_sq_of_two_le_ringKrullDim
        Onr ((q : ℕ) : Onr) hirr R hres u v huv huv' hdim
    haveI := isRegularLocalRing_uvCrossingModel Onr hOnr_max
    refine ⟨IsRegularLocalRing.of_ringEquiv e.symm.toRingEquiv, ?_, Or.inr ⟨e⟩⟩
    intro h
    apply natCast_ne_zero_uvCrossingModel Onr hOnr_max
    have h' := congrArg e h
    rwa [map_natCast, map_zero] at h'
  ·
    obtain ⟨t, -, ht⟩ :=
      CerednikDrinfeld.SpecialFormalODModule.exists_maximalIdeal_eq_map_sup_span_singleton_sup_sq_of_isProrepresentedBy_deformations_of_not_and
        Onr hOnr_complete hOnr_max ι X₀ R resR hresR Xu wu hwu hPRO hnode
    obtain ⟨e⟩ :=
      IsLocalRing.nonempty_algEquiv_powerSeries_of_maximalIdeal_eq_sup_span_singleton_sup_sq_of_two_le_ringKrullDim
        Onr R hres t ht hdim
    haveI := isRegularLocalRing_powerSeries Onr
    refine ⟨IsRegularLocalRing.of_ringEquiv e.symm.toRingEquiv, ?_, Or.inl ⟨e⟩⟩
    intro h
    apply natCast_ne_zero_powerSeries Onr hOnr_max
    have h' := congrArg e h
    rwa [map_natCast, map_zero] at h'

#print axioms solution

end S_CerednikDrinfeld_SpecialFormalODModule_isRegularLocalRing_and_nonempty_algEquiv_powerSeries_or_uvCrossingModel_of_isProrepresentedBy_deformations
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormalODModule_isRegularLocalRing_and_nonempty_algEquiv_powerSeries_or_uvCrossingModel_of_isProrepresentedBy_deformations (solution)
