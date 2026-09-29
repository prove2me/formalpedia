-- Prove2me | solution 1 for CerednikDrinfeld.exists_ringHom_range_eq_conjByFiniteIdele_forall_apply_eq_mul_of_image_kernelIdealSet_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/4a0c4e91-622d-576c-9d0d-c509c3c9732c

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_KernelIdeal
import Theorems.Thm_WeierstrassCurve_exists_image_kernelIdealSet_eq_star_smul_ofFiniteIdele_and_range_eq_conjByFiniteIdele
import Theorems.Thm_QuaternionAlgebra_range_eq_of_isMaximalOrder_of_range_eq_of_range_subset
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_conjByFiniteIdele
import Theorems.Thm_QuaternionAlgebra_IsOrder_conjByFiniteIdele
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd
import Theorems.Thm_Submodule_finiteAdeleBox_ofFiniteIdele
import Theorems.Thm_Submodule_mem_conjByFiniteIdele_diagonal_mul_iff
import Theorems.Thm_Submodule_exists_ne_zero_natCast_smul_mem_finiteAdeleBox
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_add_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_surjective_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_mem_rationalEndSubring_iff_mem_rationalHomSet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_exists_ringHom_range_eq_conjByFiniteIdele_forall_apply_eq_mul_of_image_kernelIdealSet_eq
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.Point.instFinite WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion"
p2m_attr_erase "instance" "AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆"
p2m_attr_erase "simp" "Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq"
p2m_attr_erase "simp" "ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq FrobeniusEndo.linePencil_apply WeierstrassCurve.Affine.mem_fibSet WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluX_empty WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X"
p2m_attr_erase "simp" "ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.frobPoint_zero WeierstrassCurve.frobCardHom_apply QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Quaternion TensorProduct NumberField Pointwise
p2m_open "QuaternionAlgebra~baseChange IsDedekindDomain"

noncomputable section

namespace CerednikDrinfeld
namespace DeuringExplicit

section Points

open Polynomial WeierstrassCurve

variable {F : Type*} [Field F] {k : Type*} [Field k] [Algebra F k]

abbrev Pt (k : Type*) [Field k] [Algebra F k] (W : WeierstrassCurve F) :=
  (W.baseChange k).toAffine.Point

variable [DecidableEq k]
variable {W₁ W₂ : WeierstrassCurve F}

theorem nsmul_mem_rationalHomSet [IsAlgClosed k] [W₁.IsElliptic] [W₂.IsElliptic]
    {α : Pt k W₁ →+ Pt k W₂} (hα : α ∈ rationalHomSet k W₁ W₂) (n : ℕ) : n • α ∈ rationalHomSet k W₁ W₂ := by
  induction n with
  | zero => rw [zero_nsmul]; exact zero_mem_rationalHomSet k W₁ W₂
  | succ n ih => rw [succ_nsmul]; exact add_mem_rationalHomSet k W₁ W₂ ih hα

theorem eq_zero_of_comp_eq_zero [IsAlgClosed k] [W₁.IsElliptic] [W₂.IsElliptic] {W₃ : WeierstrassCurve F}
    {α : Pt k W₁ →+ Pt k W₂} (hα : α ∈ rationalHomSet k W₁ W₂) (hα0 : α ≠ 0)
    {ρ : Pt k W₂ →+ Pt k W₃} (h : ρ.comp α = 0) : ρ = 0 := by
  ext Q
  obtain ⟨P, rfl⟩ := WeierstrassCurve.surjective_of_mem_rationalHomSet k hα hα0 Q
  exact DFunLike.congr_fun h P

end Points

section Quaternion

variable {a b : ℚ}

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

theorem star_mem_of_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {h : ℍ[ℚ, a, b]} (hh : h ∈ Λ) :
    star h ∈ Λ := by
  obtain ⟨-, t, ht⟩ := hΛ.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hh
  have e : star h = ((trd h : ℚ) : ℍ[ℚ, a, b]) - h := by
    rw [← add_star_eq_coe_trd]; abel
  have e2 : ((trd h : ℚ) : ℍ[ℚ, a, b]) = t • (1 : ℍ[ℚ, a, b]) := by
    rw [← ht, coe_intCast, zsmul_eq_mul, mul_one]
  rw [e, e2]
  exact Λ.sub_mem (Λ.smul_mem t hΛ.one_mem) hh

theorem mem_units_smul_iff (e : (ℍ[ℚ, a, b])ˣ) (I : Submodule ℤ ℍ[ℚ, a, b]) (z : ℍ[ℚ, a, b]) :
    z ∈ (e • I : Submodule ℤ ℍ[ℚ, a, b]) ↔ ((e⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * z ∈ I := by
  erw [Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨w, hw, rfl⟩
    change ((e⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * ((e : ℍ[ℚ, a, b]) * w) ∈ I
    rwa [← mul_assoc, Units.inv_mul, one_mul]
  · intro h
    exact ⟨_, h, by change (e : ℍ[ℚ, a, b]) * _ = z; rw [← mul_assoc, Units.mul_inv, one_mul]⟩

theorem mem_star_image_smul_iff (d : (ℍ[ℚ, a, b])ˣ) (I : Submodule ℤ ℍ[ℚ, a, b]) (w : ℍ[ℚ, a, b]) :
    w ∈ star '' ((d • I : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) ↔
      ((d⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * star w ∈ I := by
  constructor
  · rintro ⟨w', hw', rfl⟩
    rw [star_star]
    exact (mem_units_smul_iff d I w').mp hw'
  · intro h
    exact ⟨star w, (mem_units_smul_iff d I _).mpr h, star_star w⟩

theorem tmul_mem_finiteAdeleBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} {z : ℍ[ℚ, a, b]} (hz : z ∈ Λ) {c : 𝔸f}
    (hc : ∀ v : HeightOneSpectrum (𝓞 ℚ), c v ∈ v.adicCompletionIntegers ℚ) :
    z ⊗ₜ[ℚ] c ∈ Submodule.finiteAdeleBox Λ :=
  AddSubgroup.subset_closure ⟨z, hz, c, hc, rfl⟩

theorem one_mem_finiteAdeleBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) :
    (1 : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) ∈ Submodule.finiteAdeleBox Λ := by
  rw [Algebra.TensorProduct.one_def]
  exact tmul_mem_finiteAdeleBox hΛ.one_mem fun v => one_mem _

theorem mul_mem_finiteAdeleBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    {x y : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f} (hx : x ∈ Submodule.finiteAdeleBox Λ) (hy : y ∈ Submodule.finiteAdeleBox Λ) :
    x * y ∈ Submodule.finiteAdeleBox Λ := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hy
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨z', hz', c', hc', rfl⟩ := hx
      refine AddSubgroup.subset_closure ⟨z' * z, hΛ.mul_mem hz' hz, c' * c, fun v => ?_, ?_⟩
      · exact mul_mem (hc' v) (hc v)
      · rw [Algebra.TensorProduct.tmul_mul_tmul]
    | zero => rw [zero_mul]; exact zero_mem _
    | add u w _ _ hu hw => rw [add_mul]; exact add_mem hu hw
    | neg u _ hu =>
      convert neg_mem hu using 1
      exact neg_mul u _
  | zero => rw [mul_zero]; exact zero_mem _
  | add u w _ _ hu hw => rw [mul_add]; exact add_mem hu hw
  | neg u _ hu =>
    convert neg_mem hu using 1
    exact mul_neg x u

theorem mem_ofFiniteIdele_iff' (Λ : Submodule ℤ ℍ[ℚ, a, b]) (g : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) (z : ℍ[ℚ, a, b]) :
    z ∈ Submodule.ofFiniteIdele Λ g ↔
      ∃ w ∈ Submodule.finiteAdeleBox Λ, (g : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) * w = z ⊗ₜ[ℚ] (1 : 𝔸f) := by
  rw [Submodule.mem_ofFiniteIdele_iff, AddSubgroup.mem_map]
  rfl

theorem coe_mem_finiteAdeleBox_ofFiniteIdele {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    (g : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) :
    (g : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) ∈ Submodule.finiteAdeleBox (Submodule.ofFiniteIdele Λ g) := by
  rw [Submodule.finiteAdeleBox_ofFiniteIdele Λ hΛ.fg hΛ.spanTop g, AddSubgroup.mem_map]
  exact ⟨1, one_mem_finiteAdeleBox hΛ, by rw [AddMonoidHom.coe_mulLeft, mul_one]⟩

theorem mul_coe_mem_of_forall_mul_tmul_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    (g : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) (u : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) (B : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f))
    (hB : ∀ w ∈ B, ∀ c : 𝔸f, (∀ v : HeightOneSpectrum (𝓞 ℚ), c v ∈ v.adicCompletionIntegers ℚ) →
      w * ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) ∈ B)
    (h : ∀ z ∈ Submodule.ofFiniteIdele Λ g, u * (z ⊗ₜ[ℚ] (1 : 𝔸f)) ∈ B) :
    u * (g : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) ∈ B := by
  have hle : Submodule.finiteAdeleBox (Submodule.ofFiniteIdele Λ g) ≤ B.comap (AddMonoidHom.mulLeft u) := by
    refine (AddSubgroup.closure_le _).mpr ?_
    rintro _ ⟨z, hz, c, hc, rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_comap, AddMonoidHom.coe_mulLeft]
    have : z ⊗ₜ[ℚ] c = (z ⊗ₜ[ℚ] (1 : 𝔸f)) * ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [this, ← mul_assoc]
    exact hB _ (h z hz) c hc
  have := hle (coe_mem_finiteAdeleBox_ofFiniteIdele hΛ g)
  rw [AddSubgroup.mem_comap, AddMonoidHom.coe_mulLeft] at this
  exact this

theorem map_mulLeft_mul_tmul_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (g : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)
    (w : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) (hw : w ∈ (Submodule.finiteAdeleBox Λ).map (AddMonoidHom.mulLeft g)) (c : 𝔸f)
    (hc : ∀ v : HeightOneSpectrum (𝓞 ℚ), c v ∈ v.adicCompletionIntegers ℚ) :
    w * ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) ∈ (Submodule.finiteAdeleBox Λ).map (AddMonoidHom.mulLeft g) := by
  obtain ⟨w', hw', rfl⟩ := AddSubgroup.mem_map.mp hw
  refine AddSubgroup.mem_map.mpr ⟨w' * ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c), ?_, ?_⟩
  · exact mul_mem_finiteAdeleBox hΛ hw' (tmul_mem_finiteAdeleBox hΛ.one_mem hc)
  · change g * (w' * (1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) = g * w' * (1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c
    rw [mul_assoc]

theorem exists_natCast_mem_ofFiniteIdele {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    (g : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ∃ n : ℕ, n ≠ 0 ∧ (n : ℍ[ℚ, a, b]) ∈ Submodule.ofFiniteIdele Λ g := by
  obtain ⟨n, hn, hmem⟩ := Submodule.exists_ne_zero_natCast_smul_mem_finiteAdeleBox Λ hΛ.spanTop
    ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)
  refine ⟨n, hn, ?_⟩
  rw [mem_ofFiniteIdele_iff']
  refine ⟨_, hmem, ?_⟩
  rw [mul_smul_comm, Units.mul_inv, show (n : ℍ[ℚ, a, b]) = ((n : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b]) by
    rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul, mul_one], ← TensorProduct.smul_tmul', Algebra.TensorProduct.one_def]

theorem mem_conjByFiniteIdele_of_mul_coe_mem (Λ : Submodule ℤ ℍ[ℚ, a, b]) (g : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ)
    (u : ℍ[ℚ, a, b])
    (h : (u ⊗ₜ[ℚ] (1 : 𝔸f)) * (g : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) ∈
      (Submodule.finiteAdeleBox Λ).map (AddMonoidHom.mulLeft (g : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f))) :
    u ∈ Submodule.conjByFiniteIdele Λ g := by
  rw [Submodule.mem_conjByFiniteIdele_iff, AddSubgroup.mem_map]
  obtain ⟨w, hw, hweq⟩ := AddSubgroup.mem_map.mp h
  refine ⟨w, hw, ?_⟩
  rw [AddMonoidHom.coe_mulLeft] at hweq
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulLeft, AddMonoidHom.coe_mulRight]
  rw [hweq, mul_assoc, Units.mul_inv, mul_one]

end Quaternion

section Transport

open WeierstrassCurve

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
variable {a b : ℚ}
variable {X₁ W : WeierstrassCurve κ} [X₁.IsElliptic] [W.IsElliptic]

def compEnd {χ : Pt κ X₁ →+ Pt κ W} (hχ : χ ∈ rationalHomSet κ X₁ W) {ρ : Pt κ W →+ Pt κ X₁}
    (hρ : ρ ∈ rationalHomSet κ W X₁) : ↥(rationalEndSubring κ X₁) :=
  ⟨ρ.comp χ, Subring.subset_closure (comp_mem_rationalHomSet κ X₁ W X₁ hχ hρ)⟩

@[scoped simp] theorem coe_compEnd {χ : Pt κ X₁ →+ Pt κ W} (hχ : χ ∈ rationalHomSet κ X₁ W) {ρ : Pt κ W →+ Pt κ X₁}
    (hρ : ρ ∈ rationalHomSet κ W X₁) :
    ((compEnd hχ hρ : ↥(rationalEndSubring κ X₁)) : AddMonoid.End (Pt κ X₁)) = ρ.comp χ := rfl

def tr (θ₁ : ↥(rationalEndSubring κ X₁) →+* ℍ[ℚ, a, b]) {χ : Pt κ X₁ →+ Pt κ W} (hχ : χ ∈ rationalHomSet κ X₁ W)
    (d : (ℍ[ℚ, a, b])ˣ) {ρ : Pt κ W →+ Pt κ X₁} (hρ : ρ ∈ rationalHomSet κ W X₁) : ℍ[ℚ, a, b] :=
  ((d⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * star (θ₁ (compEnd hχ hρ))

variable {θ₁ : ↥(rationalEndSubring κ X₁) →+* ℍ[ℚ, a, b]} {χ : Pt κ X₁ →+ Pt κ W} {d : (ℍ[ℚ, a, b])ˣ}

theorem theta_compEnd_eq (hχ : χ ∈ rationalHomSet κ X₁ W) {ρ : Pt κ W →+ Pt κ X₁} (hρ : ρ ∈ rationalHomSet κ W X₁) :
    θ₁ (compEnd hχ hρ) = star ((d : ℍ[ℚ, a, b]) * tr θ₁ hχ d hρ) := by
  rw [tr, ← mul_assoc, Units.mul_inv, one_mul, star_star]

theorem tr_congr (hχ : χ ∈ rationalHomSet κ X₁ W) {ρ ρ' : Pt κ W →+ Pt κ X₁} (hρ : ρ ∈ rationalHomSet κ W X₁)
    (hρ' : ρ' ∈ rationalHomSet κ W X₁) (h : ρ = ρ') : tr θ₁ hχ d hρ = tr θ₁ hχ d hρ' := by
  subst h; rfl

theorem tr_injective (hθ₁ : Function.Injective θ₁) (hχ : χ ∈ rationalHomSet κ X₁ W) (hχ0 : χ ≠ 0)
    {ρ ρ' : Pt κ W →+ Pt κ X₁} (hρ : ρ ∈ rationalHomSet κ W X₁) (hρ' : ρ' ∈ rationalHomSet κ W X₁)
    (h : tr θ₁ hχ d hρ = tr θ₁ hχ d hρ') : ρ = ρ' := by
  have h1 : θ₁ (compEnd hχ hρ) = θ₁ (compEnd hχ hρ') := by
    rw [theta_compEnd_eq hχ hρ, theta_compEnd_eq hχ hρ', h]
  have h2 := congrArg (fun e : ↥(rationalEndSubring κ X₁) => (e : AddMonoid.End (Pt κ X₁))) (hθ₁ h1)
  simp only [coe_compEnd] at h2
  ext Q
  obtain ⟨P, rfl⟩ := WeierstrassCurve.surjective_of_mem_rationalHomSet κ hχ hχ0 Q
  exact DFunLike.congr_fun h2 P

theorem tr_comp (hχ : χ ∈ rationalHomSet κ X₁ W) (β : ↥(rationalEndSubring κ X₁))
    {ρ : Pt κ W →+ Pt κ X₁} (hρ : ρ ∈ rationalHomSet κ W X₁)
    (hβρ : ((β : AddMonoid.End (Pt κ X₁)) : Pt κ X₁ →+ Pt κ X₁).comp ρ ∈ rationalHomSet κ W X₁) :
    tr θ₁ hχ d hβρ = tr θ₁ hχ d hρ * star (θ₁ β) := by
  have : compEnd hχ hβρ = β * compEnd hχ hρ := Subtype.ext (by ext P; rfl)
  rw [tr, tr, this, map_mul, star_mul, mul_assoc]

theorem tr_zero (hχ : χ ∈ rationalHomSet κ X₁ W) (h0 : (0 : Pt κ W →+ Pt κ X₁) ∈ rationalHomSet κ W X₁) :
    tr θ₁ hχ d h0 = 0 := by
  have : compEnd hχ h0 = 0 := Subtype.ext (by rw [coe_compEnd, AddMonoidHom.zero_comp]; rfl)
  rw [tr, this, map_zero, star_zero, mul_zero]

theorem tr_add (hχ : χ ∈ rationalHomSet κ X₁ W) {ρ ρ' : Pt κ W →+ Pt κ X₁} (hρ : ρ ∈ rationalHomSet κ W X₁)
    (hρ' : ρ' ∈ rationalHomSet κ W X₁) (hadd : ρ + ρ' ∈ rationalHomSet κ W X₁) :
    tr θ₁ hχ d hadd = tr θ₁ hχ d hρ + tr θ₁ hχ d hρ' := by
  have : compEnd hχ hadd = compEnd hχ hρ + compEnd hχ hρ' :=
    Subtype.ext (by rw [coe_compEnd, AddMonoidHom.add_comp]; rfl)
  rw [tr, tr, tr, this, map_add, star_add, mul_add]

theorem tr_nsmul (hχ : χ ∈ rationalHomSet κ X₁ W) {ρ : Pt κ W →+ Pt κ X₁} (hρ : ρ ∈ rationalHomSet κ W X₁) :
    ∀ (n : ℕ) (hn : n • ρ ∈ rationalHomSet κ W X₁), tr θ₁ hχ d hn = n • tr θ₁ hχ d hρ
  | 0, hn => by
    rw [tr_congr hχ hn (zero_mem_rationalHomSet κ W X₁) (zero_nsmul ρ), tr_zero, zero_nsmul]
  | n + 1, hn => by
    rw [tr_congr hχ hn (add_mem_rationalHomSet κ W X₁ (nsmul_mem_rationalHomSet hρ n) hρ) (succ_nsmul ρ n),
      tr_add hχ (nsmul_mem_rationalHomSet hρ n) hρ, tr_nsmul hχ hρ n (nsmul_mem_rationalHomSet hρ n), succ_nsmul]

theorem clause_iff {V : WeierstrassCurve κ} [V.IsElliptic] {φ : Pt κ X₁ →+ Pt κ V} (hφ : φ ∈ rationalHomSet κ X₁ V)
    {I : Submodule ℤ ℍ[ℚ, a, b]}
    (hK : θ₁ '' kernelIdealSet κ X₁ V φ = star '' ((d • I : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b])) (z : ℍ[ℚ, a, b]) :
    z ∈ I ↔ ∃ (ρ : Pt κ V →+ Pt κ X₁) (hρ : ρ ∈ rationalHomSet κ V X₁), tr θ₁ hφ d hρ = z := by
  constructor
  · intro hz
    have h1 : star ((d : ℍ[ℚ, a, b]) * z) ∈ θ₁ '' kernelIdealSet κ X₁ V φ := by
      rw [hK, mem_star_image_smul_iff, star_star, ← mul_assoc, Units.inv_mul, one_mul]
      exact hz
    obtain ⟨e, ⟨ρ, hρ, he⟩, he'⟩ := h1
    refine ⟨ρ, hρ, ?_⟩
    have : compEnd hφ hρ = e := Subtype.ext (by rw [coe_compEnd, he])
    rw [tr, this, he', star_star, ← mul_assoc, Units.inv_mul, one_mul]
  · rintro ⟨ρ, hρ, rfl⟩
    have h1 : θ₁ (compEnd hφ hρ) ∈ θ₁ '' kernelIdealSet κ X₁ V φ := ⟨_, ⟨ρ, hρ, rfl⟩, rfl⟩
    rw [hK, mem_star_image_smul_iff] at h1
    exact h1

end Transport

section Division

variable {a b : ℚ}

theorem nrd_ne_zero (ha : a < 0) (hb : b < 0) {z : ℍ[ℚ, a, b]} (hz : z ≠ 0) : nrd z ≠ 0 := by
  intro h0
  apply hz
  have h1 : 0 ≤ z.re ^ 2 := sq_nonneg _
  have h2 : 0 ≤ -a * z.imI ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h3 : 0 ≤ -b * z.imJ ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h4 : 0 ≤ a * b * z.imK ^ 2 := mul_nonneg (mul_pos_of_neg_of_neg ha hb).le (sq_nonneg _)
  have hn : nrd z = z.re ^ 2 + -a * z.imI ^ 2 + -b * z.imJ ^ 2 + a * b * z.imK ^ 2 := by
    rw [nrd]; ring
  rw [hn] at h0
  have e1 : z.re ^ 2 = 0 := by linarith
  have e2 : -a * z.imI ^ 2 = 0 := by linarith
  have e3 : -b * z.imJ ^ 2 = 0 := by linarith
  have e4 : a * b * z.imK ^ 2 = 0 := by linarith
  have ha' : -a ≠ 0 := by linarith
  have hb' : -b ≠ 0 := by linarith
  have hab : a * b ≠ 0 := (mul_pos_of_neg_of_neg ha hb).ne'
  ext
  · simpa using e1
  · simpa [ha.ne] using e2
  · simpa [hb.ne] using e3
  · simpa [hab] using e4

def invQ (z : ℍ[ℚ, a, b]) : ℍ[ℚ, a, b] := (nrd z)⁻¹ • star z

theorem mul_invQ (ha : a < 0) (hb : b < 0) {z : ℍ[ℚ, a, b]} (hz : z ≠ 0) : z * invQ z = 1 := by
  rw [invQ, mul_smul_comm, mul_star_eq_coe_nrd, smul_coe, inv_mul_cancel₀ (nrd_ne_zero ha hb hz)]
  rfl

theorem invQ_mul (ha : a < 0) (hb : b < 0) {z : ℍ[ℚ, a, b]} (hz : z ≠ 0) : invQ z * z = 1 := by
  rw [invQ, smul_mul_assoc, star_mul_eq_coe_nrd, smul_coe, inv_mul_cancel₀ (nrd_ne_zero ha hb hz)]
  rfl

def unitOf (ha : a < 0) (hb : b < 0) (z : ℍ[ℚ, a, b]) (hz : z ≠ 0) : (ℍ[ℚ, a, b])ˣ :=
  ⟨z, invQ z, mul_invQ ha hb hz, invQ_mul ha hb hz⟩

theorem mul_right_cancel_of_ne_zero (ha : a < 0) (hb : b < 0) {z u w : ℍ[ℚ, a, b]} (hz : z ≠ 0)
    (h : u * z = w * z) : u = w := by
  have := congrArg (· * invQ z) h
  simpa only [mul_assoc, mul_invQ ha hb hz, mul_one] using this

theorem mul_left_cancel_of_ne_zero (ha : a < 0) (hb : b < 0) {z u w : ℍ[ℚ, a, b]} (hz : z ≠ 0)
    (h : z * u = z * w) : u = w := by
  have := congrArg (invQ z * ·) h
  simpa only [← mul_assoc, invQ_mul ha hb hz, one_mul] using this

theorem nsmul_right_cancel {n : ℕ} (hn : n ≠ 0) {z w : ℍ[ℚ, a, b]} (h : n • z = n • w) : z = w := by
  have h' : (n : ℚ) • z = (n : ℚ) • w := by
    simpa only [Nat.cast_smul_eq_nsmul] using h
  exact smul_right_injective ℍ[ℚ, a, b] (Nat.cast_ne_zero.mpr hn) h'

end Division

section Action

open WeierstrassCurve

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
variable {a b : ℚ}
variable {X₁ W : WeierstrassCurve κ} [X₁.IsElliptic] [W.IsElliptic]

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

structure DFrame (Λ₁ : Submodule ℤ ℍ[ℚ, a, b]) (θ₁ : ↥(rationalEndSubring κ X₁) →+* ℍ[ℚ, a, b])
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (χ : Pt κ X₁ →+ Pt κ W) (d : (ℍ[ℚ, a, b])ˣ) : Prop where
  neg_a : a < 0
  neg_b : b < 0
  isOrder : IsOrder Λ₁
  inj : Function.Injective θ₁
  range_eq : Set.range θ₁ = (Λ₁ : Set ℍ[ℚ, a, b])
  mem : χ ∈ rationalHomSet κ X₁ W
  ne_zero : χ ≠ 0
  hK : θ₁ '' kernelIdealSet κ X₁ W χ = star '' ((d • Submodule.ofFiniteIdele Λ₁ x : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b])

variable {Λ₁ : Submodule ℤ ℍ[ℚ, a, b]} {θ₁ : ↥(rationalEndSubring κ X₁) →+* ℍ[ℚ, a, b]}
  {x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ} {χ : Pt κ X₁ →+ Pt κ W} {d : (ℍ[ℚ, a, b])ˣ}

abbrev toHom (α : ↥(rationalEndSubring κ W)) : Pt κ W →+ Pt κ W :=
  ((α : AddMonoid.End (Pt κ W)) : Pt κ W →+ Pt κ W)

theorem toHom_mem (α : ↥(rationalEndSubring κ W)) : toHom α ∈ rationalHomSet κ W W :=
  (WeierstrassCurve.mem_rationalEndSubring_iff_mem_rationalHomSet κ W _).mp α.2

theorem comp_toHom_mem {ρ : Pt κ W →+ Pt κ X₁} (hρ : ρ ∈ rationalHomSet κ W X₁) (α : ↥(rationalEndSubring κ W)) :
    ρ.comp (toHom α) ∈ rationalHomSet κ W X₁ :=
  comp_mem_rationalHomSet κ W W X₁ (toHom_mem α) hρ

@[scoped simp] theorem toHom_one : toHom (1 : ↥(rationalEndSubring κ W)) = AddMonoidHom.id _ := rfl

@[scoped simp] theorem toHom_mul (α β : ↥(rationalEndSubring κ W)) : toHom (α * β) = (toHom α).comp (toHom β) := rfl

@[scoped simp] theorem toHom_add (α β : ↥(rationalEndSubring κ W)) : toHom (α + β) = toHom α + toHom β := rfl

@[scoped simp] theorem toHom_zero : toHom (0 : ↥(rationalEndSubring κ W)) = 0 := rfl

theorem DFrame.clause_x (hF : DFrame Λ₁ θ₁ x χ d) (z : ℍ[ℚ, a, b]) :
    z ∈ Submodule.ofFiniteIdele Λ₁ x ↔ ∃ (ρ : Pt κ W →+ Pt κ X₁) (hρ : ρ ∈ rationalHomSet κ W X₁), tr θ₁ hF.mem d hρ = z :=
  clause_iff hF.mem hF.hK z

theorem DFrame.eq_zero_of_tr_eq_zero (hF : DFrame Λ₁ θ₁ x χ d) {ρ : Pt κ W →+ Pt κ X₁}
    (hρ : ρ ∈ rationalHomSet κ W X₁) (h : tr θ₁ hF.mem d hρ = 0) : ρ = 0 :=
  tr_injective hF.inj hF.mem hF.ne_zero hρ (zero_mem_rationalHomSet κ W X₁) (h.trans (tr_zero hF.mem _).symm)

theorem DFrame.exists_rho0 (hF : DFrame Λ₁ θ₁ x χ d) :
    ∃ (ρ₀ : Pt κ W →+ Pt κ X₁) (hρ₀ : ρ₀ ∈ rationalHomSet κ W X₁), tr θ₁ hF.mem d hρ₀ ≠ 0 := by
  obtain ⟨n, hn, hmem⟩ := exists_natCast_mem_ofFiniteIdele hF.isOrder x
  obtain ⟨ρ₀, hρ₀, h⟩ := (hF.clause_x _).mp hmem
  refine ⟨ρ₀, hρ₀, ?_⟩
  rw [h]
  intro h0
  apply hn
  have := congrArg QuaternionAlgebra.re h0
  simpa using this

def DFrame.rho0 (hF : DFrame Λ₁ θ₁ x χ d) : Pt κ W →+ Pt κ X₁ := hF.exists_rho0.choose

theorem DFrame.rho0_mem (hF : DFrame Λ₁ θ₁ x χ d) : hF.rho0 ∈ rationalHomSet κ W X₁ :=
  hF.exists_rho0.choose_spec.choose

def DFrame.z0 (hF : DFrame Λ₁ θ₁ x χ d) : ℍ[ℚ, a, b] := tr θ₁ hF.mem d hF.rho0_mem

theorem DFrame.z0_ne_zero (hF : DFrame Λ₁ θ₁ x χ d) : hF.z0 ≠ 0 :=
  hF.exists_rho0.choose_spec.choose_spec

theorem DFrame.rho0_ne_zero (hF : DFrame Λ₁ θ₁ x χ d) : hF.rho0 ≠ 0 := by
  intro h
  apply hF.z0_ne_zero
  rw [DFrame.z0, tr_congr hF.mem hF.rho0_mem (zero_mem_rationalHomSet κ W X₁) h, tr_zero]

def DFrame.hmap (hF : DFrame Λ₁ θ₁ x χ d) (α : ↥(rationalEndSubring κ W)) : ℍ[ℚ, a, b] :=
  tr θ₁ hF.mem d (comp_toHom_mem hF.rho0_mem α) * invQ hF.z0

theorem DFrame.hmap_mul_z0 (hF : DFrame Λ₁ θ₁ x χ d) (α : ↥(rationalEndSubring κ W)) :
    hF.hmap α * hF.z0 = tr θ₁ hF.mem d (comp_toHom_mem hF.rho0_mem α) := by
  rw [DFrame.hmap, mul_assoc, invQ_mul hF.neg_a hF.neg_b hF.z0_ne_zero, mul_one]

theorem DFrame.exists_beta (hF : DFrame Λ₁ θ₁ x χ d) {w : ℍ[ℚ, a, b]} (hw : w ∈ Λ₁) :
    ∃ β : ↥(rationalEndSubring κ X₁), star (θ₁ β) = w := by
  have hsw : star w ∈ Set.range θ₁ := by rw [hF.range_eq]; exact star_mem_of_mem hF.isOrder hw
  obtain ⟨β, hβ⟩ := hsw
  exact ⟨β, by rw [hβ, star_star]⟩

theorem beta_comp_mem {ρ : Pt κ W →+ Pt κ X₁} (hρ : ρ ∈ rationalHomSet κ W X₁) (β : ↥(rationalEndSubring κ X₁)) :
    ((β : AddMonoid.End (Pt κ X₁)) : Pt κ X₁ →+ Pt κ X₁).comp ρ ∈ rationalHomSet κ W X₁ :=
  comp_mem_rationalHomSet κ W X₁ X₁ hρ
    ((WeierstrassCurve.mem_rationalEndSubring_iff_mem_rationalHomSet κ X₁ _).mp β.2)

theorem DFrame.exists_nsmul_eq_comp (hF : DFrame Λ₁ θ₁ x χ d) {ρ : Pt κ W →+ Pt κ X₁}
    (hρ : ρ ∈ rationalHomSet κ W X₁) :
    ∃ n : ℕ, n ≠ 0 ∧ ∃ β : ↥(rationalEndSubring κ X₁),
      ((β : AddMonoid.End (Pt κ X₁)) : Pt κ X₁ →+ Pt κ X₁).comp hF.rho0 = n • ρ := by
  set y : ℍ[ℚ, a, b] := invQ hF.z0 * tr θ₁ hF.mem d hρ with hy
  have hyspan : y ∈ Submodule.span ℚ (Λ₁ : Set ℍ[ℚ, a, b]) := by rw [hF.isOrder.spanTop]; trivial
  obtain ⟨n, hn, hny⟩ := exists_natCast_smul_mem_of_mem_span hyspan
  obtain ⟨β, hβ⟩ := hF.exists_beta hny
  refine ⟨n, hn, β, ?_⟩
  refine tr_injective (d := d) hF.inj hF.mem hF.ne_zero (beta_comp_mem hF.rho0_mem β) (nsmul_mem_rationalHomSet hρ n) ?_
  rw [tr_comp hF.mem β hF.rho0_mem, hβ, tr_nsmul hF.mem hρ n, natCast_zsmul, hy, mul_smul_comm, ← mul_assoc]
  congr 1
  change hF.z0 * invQ hF.z0 * _ = _
  rw [mul_invQ hF.neg_a hF.neg_b hF.z0_ne_zero, one_mul]

theorem DFrame.tr_comp_toHom (hF : DFrame Λ₁ θ₁ x χ d) {ρ : Pt κ W →+ Pt κ X₁} (hρ : ρ ∈ rationalHomSet κ W X₁)
    (α : ↥(rationalEndSubring κ W)) :
    tr θ₁ hF.mem d (comp_toHom_mem hρ α) = hF.hmap α * tr θ₁ hF.mem d hρ := by
  obtain ⟨n, hn, β, hβ⟩ := hF.exists_nsmul_eq_comp hρ
  apply nsmul_right_cancel hn

  have hnρα : n • ρ.comp (toHom α) ∈ rationalHomSet κ W X₁ := nsmul_mem_rationalHomSet (comp_toHom_mem hρ α) n
  have hβρ₀α : ((β : AddMonoid.End (Pt κ X₁)) : Pt κ X₁ →+ Pt κ X₁).comp (hF.rho0.comp (toHom α)) ∈
      rationalHomSet κ W X₁ := beta_comp_mem (comp_toHom_mem hF.rho0_mem α) β
  have e1 : n • tr θ₁ hF.mem d (comp_toHom_mem hρ α) = tr θ₁ hF.mem d hnρα := (tr_nsmul hF.mem _ n hnρα).symm
  have e2 : tr θ₁ hF.mem d hnρα = tr θ₁ hF.mem d hβρ₀α := by
    refine tr_congr hF.mem _ _ ?_
    rw [← AddMonoidHom.comp_assoc, hβ]
    ext P
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.nsmul_apply]
  have e3 : tr θ₁ hF.mem d hβρ₀α = hF.hmap α * hF.z0 * star (θ₁ β) := by
    rw [tr_comp hF.mem β (comp_toHom_mem hF.rho0_mem α), hF.hmap_mul_z0]
  have e4 : hF.z0 * star (θ₁ β) = tr θ₁ hF.mem d (beta_comp_mem hF.rho0_mem β) := by
    rw [DFrame.z0, tr_comp hF.mem β hF.rho0_mem]
  have e5 : tr θ₁ hF.mem d (beta_comp_mem hF.rho0_mem β) = n • tr θ₁ hF.mem d hρ := by
    rw [tr_congr hF.mem _ (nsmul_mem_rationalHomSet hρ n) hβ, tr_nsmul hF.mem hρ n]
  rw [e1, e2, e3, mul_assoc, e4, e5, mul_smul_comm]

theorem DFrame.hmap_one (hF : DFrame Λ₁ θ₁ x χ d) : hF.hmap 1 = 1 := by
  apply mul_right_cancel_of_ne_zero hF.neg_a hF.neg_b hF.z0_ne_zero
  rw [hF.hmap_mul_z0, one_mul, DFrame.z0]

theorem DFrame.hmap_mul (hF : DFrame Λ₁ θ₁ x χ d) (α β : ↥(rationalEndSubring κ W)) :
    hF.hmap (α * β) = hF.hmap β * hF.hmap α := by
  apply mul_right_cancel_of_ne_zero hF.neg_a hF.neg_b hF.z0_ne_zero
  rw [hF.hmap_mul_z0, mul_assoc, hF.hmap_mul_z0]
  have h1 := hF.tr_comp_toHom (comp_toHom_mem hF.rho0_mem α) β
  rw [← h1]

theorem DFrame.hmap_add (hF : DFrame Λ₁ θ₁ x χ d) (α β : ↥(rationalEndSubring κ W)) :
    hF.hmap (α + β) = hF.hmap α + hF.hmap β := by
  rw [DFrame.hmap, DFrame.hmap, DFrame.hmap, ← add_mul]
  congr 1
  rw [← tr_add hF.mem (comp_toHom_mem hF.rho0_mem α) (comp_toHom_mem hF.rho0_mem β)
    (add_mem_rationalHomSet κ W X₁ (comp_toHom_mem hF.rho0_mem α) (comp_toHom_mem hF.rho0_mem β))]
  exact tr_congr hF.mem _ _ (by rw [toHom_add, AddMonoidHom.comp_add])

theorem DFrame.hmap_zero (hF : DFrame Λ₁ θ₁ x χ d) : hF.hmap 0 = 0 := by
  have := hF.hmap_add 0 0
  rw [add_zero] at this
  exact left_eq_add.mp this

theorem DFrame.hmap_injective (hF : DFrame Λ₁ θ₁ x χ d) {α : ↥(rationalEndSubring κ W)} (h : hF.hmap α = 0) :
    α = 0 := by
  have h1 : tr θ₁ hF.mem d (comp_toHom_mem hF.rho0_mem α) = 0 := by rw [← hF.hmap_mul_z0, h, zero_mul]
  have h2 : hF.rho0.comp (toHom α) = 0 := hF.eq_zero_of_tr_eq_zero _ h1
  by_contra hα
  have hα' : toHom α ≠ 0 := by
    intro h0
    apply hα
    exact Subtype.ext h0
  exact hF.rho0_ne_zero (eq_zero_of_comp_eq_zero (toHom_mem α) hα' h2)

theorem DFrame.box_stable (hF : DFrame Λ₁ θ₁ x χ d) :
    ∀ w ∈ (Submodule.finiteAdeleBox Λ₁).map (AddMonoidHom.mulLeft (x : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)),
      ∀ c : 𝔸f, (∀ v : HeightOneSpectrum (𝓞 ℚ), c v ∈ v.adicCompletionIntegers ℚ) →
        w * ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) ∈ (Submodule.finiteAdeleBox Λ₁).map (AddMonoidHom.mulLeft (x : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)) :=
  fun w hw c hc => map_mulLeft_mul_tmul_mem hF.isOrder _ w hw c hc

theorem DFrame.hmap_mem (hF : DFrame Λ₁ θ₁ x χ d) (α : ↥(rationalEndSubring κ W)) :
    hF.hmap α ∈ Submodule.conjByFiniteIdele Λ₁ x := by
  refine mem_conjByFiniteIdele_of_mul_coe_mem Λ₁ x _ ?_
  refine mul_coe_mem_of_forall_mul_tmul_mem hF.isOrder x _ _ hF.box_stable fun z hz => ?_
  obtain ⟨ρ, hρ, rfl⟩ := (hF.clause_x z).mp hz
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← hF.tr_comp_toHom hρ α]
  have : tr θ₁ hF.mem d (comp_toHom_mem hρ α) ∈ Submodule.ofFiniteIdele Λ₁ x :=
    (hF.clause_x _).mpr ⟨_, comp_toHom_mem hρ α, rfl⟩
  rwa [Submodule.mem_ofFiniteIdele_iff] at this

def DFrame.thetaW (hF : DFrame Λ₁ θ₁ x χ d) : ↥(rationalEndSubring κ W) →+* ℍ[ℚ, a, b] where
  toFun α := star ((d : ℍ[ℚ, a, b]) * hF.hmap α * ((d⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]))
  map_one' := by rw [hF.hmap_one, mul_one, Units.mul_inv, star_one]
  map_mul' α β := by
    rw [hF.hmap_mul, ← star_mul]
    congr 1
    simp only [mul_assoc, Units.inv_mul_cancel_left]
  map_zero' := by rw [hF.hmap_zero, mul_zero, zero_mul, star_zero]
  map_add' α β := by rw [hF.hmap_add, mul_add, add_mul, star_add]

theorem DFrame.thetaW_apply (hF : DFrame Λ₁ θ₁ x χ d) (α : ↥(rationalEndSubring κ W)) :
    hF.thetaW α = star ((d : ℍ[ℚ, a, b]) * hF.hmap α * ((d⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) := rfl

theorem DFrame.thetaW_injective (hF : DFrame Λ₁ θ₁ x χ d) : Function.Injective hF.thetaW := by
  rw [injective_iff_map_eq_zero]
  intro α hα
  rw [hF.thetaW_apply, star_eq_zero] at hα
  apply hF.hmap_injective
  have : ((d⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * ((d : ℍ[ℚ, a, b]) * hF.hmap α * ((d⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) *
      (d : ℍ[ℚ, a, b]) = 0 := by rw [hα, mul_zero, zero_mul]
  simpa only [mul_assoc, Units.inv_mul_cancel_left, Units.inv_mul, mul_one] using this

theorem DFrame.thetaW_mem (hF : DFrame Λ₁ θ₁ x χ d) (α : ↥(rationalEndSubring κ W)) :
    hF.thetaW α ∈ Submodule.conjByFiniteIdele Λ₁ (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] d * x) := by
  have hO : IsOrder (Submodule.conjByFiniteIdele Λ₁ (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] d * x)) :=
    QuaternionAlgebra.IsOrder.conjByFiniteIdele Λ₁ hF.isOrder _
  rw [hF.thetaW_apply]
  refine star_mem_of_mem hO ?_
  rw [Submodule.mem_conjByFiniteIdele_diagonal_mul_iff]
  simpa only [mul_assoc, Units.inv_mul_cancel_left, Units.inv_mul, mul_one] using hF.hmap_mem α

theorem DFrame.law (hF : DFrame Λ₁ θ₁ x χ d) {ρ : Pt κ W →+ Pt κ X₁} (hρ : ρ ∈ rationalHomSet κ W X₁)
    (α : ↥(rationalEndSubring κ W)) (e e' : ↥(rationalEndSubring κ X₁))
    (he : (e : AddMonoid.End (Pt κ X₁)) = ρ.comp χ)
    (he' : (e' : AddMonoid.End (Pt κ X₁)) = (ρ.comp (toHom α)).comp χ) :
    θ₁ e' = θ₁ e * hF.thetaW α := by
  have h1 : e = compEnd hF.mem hρ := Subtype.ext (by rw [coe_compEnd, he])
  have h2 : e' = compEnd hF.mem (comp_toHom_mem hρ α) := Subtype.ext (by rw [coe_compEnd, he'])
  rw [h1, h2, theta_compEnd_eq (d := d) hF.mem hρ, theta_compEnd_eq (d := d) hF.mem (comp_toHom_mem hρ α),
    hF.tr_comp_toHom hρ α, hF.thetaW_apply, ← star_mul]
  congr 1
  simp only [mul_assoc, Units.inv_mul_cancel_left]

end Action

end CerednikDrinfeld.DeuringExplicit
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_ringHom_range_eq_conjByFiniteIdele_forall_apply_eq_mul_of_image_kernelIdealSet_eq.CerednikDrinfeld P2MW.S_CerednikDrinfeld_exists_ringHom_range_eq_conjByFiniteIdele_forall_apply_eq_mul_of_image_kernelIdealSet_eq.CerednikDrinfeld.DeuringExplicit"
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_ringHom_range_eq_conjByFiniteIdele_forall_apply_eq_mul_of_image_kernelIdealSet_eq.CerednikDrinfeld"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_ringHom_range_eq_conjByFiniteIdele_forall_apply_eq_mul_of_image_kernelIdealSet_eq.CerednikDrinfeld P2MW.S_CerednikDrinfeld_exists_ringHom_range_eq_conjByFiniteIdele_forall_apply_eq_mul_of_image_kernelIdealSet_eq.CerednikDrinfeld.DeuringExplicit"

open CerednikDrinfeld.DeuringExplicit WeierstrassCurve in
theorem solution
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (q' : ℕ) [Fact q'.Prime] [CharP κ q'] [Algebra (ZMod q') κ] [Algebra.IsAlgebraic (ZMod q') κ]
    (X₁ : WeierstrassCurve κ) [X₁.IsElliptic] (hss : ∀ P : X₁.toAffine.Point, q' • P = 0 → P = 0)
    (a b : ℚ) (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ₁ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ₁ : IsMaximalOrder Λ₁)
    (θ₁ : ↥(WeierstrassCurve.rationalEndSubring κ X₁) →+* ℍ[ℚ, a, b])
    (hθ₁ : Function.Injective θ₁) (hθ₁Λ : Set.range θ₁ = (Λ₁ : Set ℍ[ℚ, a, b]))
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (W : WeierstrassCurve κ) [W.IsElliptic] (χ : X₁.toAffine.Point →+ W.toAffine.Point)
    (hχ : χ ∈ WeierstrassCurve.rationalHomSet κ X₁ W) (hχ0 : χ ≠ 0) (d : (ℍ[ℚ, a, b])ˣ)
    (hK : θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W χ =
      star '' ((d • Submodule.ofFiniteIdele Λ₁ x : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b])) :
    ∃ θW : ↥(WeierstrassCurve.rationalEndSubring κ W) →+* ℍ[ℚ, a, b],
      Function.Injective θW ∧
      Set.range θW =
        (Submodule.conjByFiniteIdele Λ₁ (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] d * x) : Set ℍ[ℚ, a, b]) ∧
      ∀ ρ ∈ WeierstrassCurve.rationalHomSet κ W X₁, ∀ (α : ↥(WeierstrassCurve.rationalEndSubring κ W))
        (e e' : ↥(WeierstrassCurve.rationalEndSubring κ X₁)),
        (e : AddMonoid.End (X₁.baseChange κ).toAffine.Point) = ρ.comp χ →
        (e' : AddMonoid.End (X₁.baseChange κ).toAffine.Point) =
          (ρ.comp ((α : AddMonoid.End (W.baseChange κ).toAffine.Point) :
            (W.baseChange κ).toAffine.Point →+ (W.baseChange κ).toAffine.Point)).comp χ →
        θ₁ e' = θ₁ e * θW α := by
  have hF : DFrame (X₁ := X₁) (W := W) Λ₁ θ₁ x χ d :=
    ⟨hdef.neg_left, hdef.neg_right, hΛ₁.isOrder, hθ₁, hθ₁Λ, hχ, hχ0, hK⟩

  obtain ⟨d₀, x₀, -, θ₀, hθ₀, hθ₀range⟩ :=
    WeierstrassCurve.exists_image_kernelIdealSet_eq_star_smul_ofFiniteIdele_and_range_eq_conjByFiniteIdele
      q' X₁ hss a b hdef Λ₁ hΛ₁ θ₁ hθ₁ hθ₁Λ W χ hχ hχ0
  have hmax₀ : IsMaximalOrder (Submodule.conjByFiniteIdele Λ₁ x₀) := hΛ₁.conjByFiniteIdele x₀
  have hmax : IsMaximalOrder (Submodule.conjByFiniteIdele Λ₁ (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] d * x)) :=
    hΛ₁.conjByFiniteIdele _
  have hsub : Set.range hF.thetaW ⊆
      (Submodule.conjByFiniteIdele Λ₁ (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] d * x) : Set ℍ[ℚ, a, b]) := by
    rintro _ ⟨α, rfl⟩
    exact hF.thetaW_mem α
  have hrange := QuaternionAlgebra.range_eq_of_isMaximalOrder_of_range_eq_of_range_subset θ₀ hF.thetaW hθ₀
    hF.thetaW_injective hmax₀ hmax hθ₀range hsub
  exact ⟨hF.thetaW, hF.thetaW_injective, hrange, fun ρ hρ α e e' he he' => hF.law hρ α e e' he he'⟩

end S_CerednikDrinfeld_exists_ringHom_range_eq_conjByFiniteIdele_forall_apply_eq_mul_of_image_kernelIdealSet_eq
end P2MW
export P2MW.S_CerednikDrinfeld_exists_ringHom_range_eq_conjByFiniteIdele_forall_apply_eq_mul_of_image_kernelIdealSet_eq (solution)
