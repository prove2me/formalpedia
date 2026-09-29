-- Prove2me | solution 1 for CerednikDrinfeld.Omega.isCurveOver_invariantFieldOf_inf_typePreserving_of_exists_relIndex_ne_zero_of_exists_not_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/60b9896c-85ef-5f63-99d2-6c01887302e6

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_AlgebraicCurve_TotallyDegenerateCovering
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_CerednikDrinfeld_Ribbon

import Theorems.Thm_CerednikDrinfeld_Omega_exists_transcendental_finiteDimensional_adjoin_invariantFieldOf_of_exists_relIndex_ne_zero_of_exists_not_mem_range
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_isCurveOver_invariantFieldOf_inf_typePreserving_of_exists_relIndex_ne_zero_of_exists_not_mem_range
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq LocalGL2.swapUnit_val CerednikDrinfeld.Omega.coordSub_apply CerednikDrinfeld.Omega.coord_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford AlgebraicCurve

theorem solution

    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    [CompleteSpace K] [IsAlgClosed K]
    (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀]
    [Finite (IsLocalRing.ResidueField R₀)]
    (hR₀ : ∀ x : K₀, x ∈ Set.range (algebraMap R₀ K₀) ↔ Valued.v (algebraMap K₀ K x) ≤ 1)

    (ϖ : Omega.PseudoUniformizer K₀ K) (ϖ₀ : R₀) (hϖ₀ : Irreducible ϖ₀) (hϖ : algebraMap R₀ K₀ ϖ₀ = ϖ.ϖ)
    (hex : Omega.IsExhausted ϖ)

    (G : Type) [Group G] (ρ : G →* PGL(2, K₀))
    [MulAction G (LT.LatticeTree.Vertex R₀ K₀)]
    [Mumford.GraphAction G (BruhatTits.tree R₀ K₀)]
    (hact : Mumford.ActsThrough (LT.LatticeTree.Vertex R₀ K₀) ρ)
    [IsDomain (Omega.HolRingOf ϖ ρ)]

    (Γ : Subgroup G)
    (hfin : ∀ d : (BruhatTits.tree R₀ K₀).Dart, Finite (MulAction.stabilizer (↥(Γ.map ρ)) d))
    [Fintype (Mumford.QuotVert Γ (LT.LatticeTree.Vertex R₀ K₀))]
    [Fintype (Mumford.QuotEdge Γ (BruhatTits.tree R₀ K₀))]
    (hexch : ∃ γ : G, γ ∈ Γ ∧ γ ∉ Mumford.typePreserving G (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))

    (hvtf : ∃ Γ'' : Subgroup G, Γ'' ≤ Γ ⊓ Mumford.typePreserving G (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) ∧
      Γ''.relIndex (Γ ⊓ Mumford.typePreserving G (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀)) ≠ 0 ∧
      ∀ g ∈ Γ''.map ρ, IsOfFinOrder g → g = 1)

    (hnc : ∃ x : ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) (Γ ⊓ Mumford.typePreserving G (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))),
      x ∉ Set.range (algebraMap K ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) (Γ ⊓ Mumford.typePreserving G (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))))) :
    IsCurveOver K ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) (Γ ⊓ Mumford.typePreserving G (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))) ∧
    Algebra.EssFiniteType K ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) (Γ ⊓ Mumford.typePreserving G (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))) ∧
    ∃ x : ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) (Γ ⊓ Mumford.typePreserving G (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))), Transcendental K x ∧
      FiniteDimensional ↥(IntermediateField.adjoin K ({x} : Set ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) (Γ ⊓ Mumford.typePreserving G (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))))) ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) (Γ ⊓ Mumford.typePreserving G (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))) := by
  obtain ⟨x, hx, hfd⟩ :=
    CerednikDrinfeld.Omega.exists_transcendental_finiteDimensional_adjoin_invariantFieldOf_of_exists_relIndex_ne_zero_of_exists_not_mem_range
      K₀ K hrk R₀ hR₀ ϖ ϖ₀ hϖ₀ hϖ hex G ρ hact Γ hfin hexch hvtf hnc
  haveI := hfd
  exact ⟨AlgebraicCurve.isCurveOver_of_isAlgClosed_of_transcendental x hx,
    AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional hx hfd, x, hx, hfd⟩

end S_CerednikDrinfeld_Omega_isCurveOver_invariantFieldOf_inf_typePreserving_of_exists_relIndex_ne_zero_of_exists_not_mem_range
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_isCurveOver_invariantFieldOf_inf_typePreserving_of_exists_relIndex_ne_zero_of_exists_not_mem_range (solution)
