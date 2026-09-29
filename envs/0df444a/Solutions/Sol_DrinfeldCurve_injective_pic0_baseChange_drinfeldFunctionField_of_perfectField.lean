-- Prove2me | solution 1 for DrinfeldCurve.injective_pic0_baseChange_drinfeldFunctionField_of_perfectField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/1b27b7c8-3653-5fc1-9921-7a2cbccb3f09

import Definitions.Def_AlgebraicCurve_Pic0BaseChange
import Definitions.Def_DrinfeldCurve_MapConstants
import Theorems.Thm_AlgebraicCurve_Divisor_isPrincipal_of_isPrincipal_pullbackConstants_of_isConstantFieldExtension
import Theorems.Thm_DrinfeldCurve_constantsAreBase_drinfeldFunctionField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DrinfeldCurve_injective_pic0_baseChange_drinfeldFunctionField_of_perfectField
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false

open AlgebraicCurve DrinfeldCurve

private theorem pic0_mk_eq_zero_iff {K F : Type*} [Field K] [Field F] [Algebra K F]
    (D : Divisor.degZero (K := K) (F := F)) : Pic0.mk D = 0 ↔ (D : Divisor K F).IsPrincipal :=
  (QuotientAddGroup.eq_zero_iff D).trans (AddSubgroup.mem_addSubgroupOf.trans Divisor.mem_principal)

attribute [local instance 10] constantsAlgebraCoordRing functionFieldConstantsAlgebra in
attribute [local instance] isIntegral_functionFieldMapConstants in

theorem solution
    (q : ℕ) [Fact q.Prime] (k K : Type) [Field k] [Field K] [PerfectField k] [Algebra k K] [Algebra.IsAlgebraic k K]
    [Algebra (GaloisField q 2) k] [Algebra (GaloisField q 2) K] [IsScalarTower (GaloisField q 2) k K]
    [IsDomain (CoordRing q k)] [IsDomain (CoordRing q K)] [HasPrincipalDivisors K (drinfeldFunctionField q K)]
    [ConstantFieldDegreeFormula k K (drinfeldFunctionField q k) (drinfeldFunctionField q K)] :
    Function.Injective (Pic0.baseChange k K (drinfeldFunctionField q k) (drinfeldFunctionField q K)) := by
  refine (injective_iff_map_eq_zero _).mpr fun c hc => ?_
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective c
  rw [Pic0.baseChange_mk, pic0_mk_eq_zero_iff] at hc
  rw [pic0_mk_eq_zero_iff]
  exact Divisor.isPrincipal_of_isPrincipal_pullbackConstants_of_isConstantFieldExtension
    (adjoin_range_algebraMap_eq_top q k K) (constantsAreBase_drinfeldFunctionField q k).1 hc

end S_DrinfeldCurve_injective_pic0_baseChange_drinfeldFunctionField_of_perfectField
end P2MW
export P2MW.S_DrinfeldCurve_injective_pic0_baseChange_drinfeldFunctionField_of_perfectField (solution)
