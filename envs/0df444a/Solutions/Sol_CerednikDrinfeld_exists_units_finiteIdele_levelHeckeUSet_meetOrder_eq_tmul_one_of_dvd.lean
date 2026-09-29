-- Prove2me | solution 1 for CerednikDrinfeld.exists_units_finiteIdele_levelHeckeUSet_meetOrder_eq_tmul_one_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/5ab91e90-189a-5b3e-8c3c-884803e399be

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Theorems.Thm_CerednikDrinfeld_CSTower_exists_finiteIdeleDiagonal_mul_inv_mem_levelHeckeUSet_meetOrder_isEichlerOrder_of_dvd
import Theorems.Thm_CerednikDrinfeld_levelHeckeUSet_eq_doubleCoset_finiteIdeleStabilizer_of_dvd_of_squarefree
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_eq_finiteIdeleDiagonal_mul_mul_of_forall_nrd_eq_one
import Theorems.Thm_QuaternionAlgebra_IsDefiniteRamifiedExactlyAt_exists_nrd_eq_of_pos
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_exists_mem_finiteIdeleStabilizer_forall_nrd_eq
import Theorems.Thm_CerednikDrinfeld_CosetGraph_exists_mem_awayUnits_nrd_eq
import Theorems.Thm_QuaternionAlgebra_exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
import Theorems.Thm_QuaternionAlgebra_IsOrder_mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_int_trd_eq_and_nrd_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_exists_units_finiteIdele_levelHeckeUSet_meetOrder_eq_tmul_one_of_dvd
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.SpecializationWitnessData.addCommGroup ModularCurve.CommutingHeckeFamily.commRing_adjoin ModularCurve.Gamma0Pair.isElliptic ModularCurve.ModuliTestDatum.isElliptic_reduced ModularCurve.ModuliTestDatum.isElliptic_curve ModularCurve.ModuliTestDatum.isElliptic_generic"
p2m_attr_erase "simp" "LocalGL2.swapUnit_val QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul ModularCurve.coe_levelAlphaC ModularCurve.SSLevelDatum.mk.sizeOf_spec ModularCurve.SSLevelDatum.mk.injEq ModularCurve.coe_levelBetaC ModularCurve.coe_heckeBetaC AlgebraicCurve.Divisor.coe_degZeroEnd ModularCurve.coe_heckeAlphaC AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.CommutingHeckeFamily.mk.injEq ModularCurve.SpecializationWitnessData.mk.sizeOf_spec ModularCurve.SpecializationWitnessData.mk.injEq ModularCurve.CommutingHeckeFamily.mk.sizeOf_spec ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg"
p2m_attr_erase "simp" "ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.ComapPlace.place_toValuationSubring ModularCurve.ModuliTestDatum.restrictLevel_emb ModularCurve.ModuliTestDatum.restrictLevel_res ModularCurve.ModuliTestDatum.mk.injEq ModularCurve.ModuliTestDatum.restrictLevel_W ModularCurve.ModuliTestDatum.place_toValuationSubring ModularCurve.ModuliTestDatum.restrictLevel_curve ModularCurve.ModuliTestDatum.resEquiv_apply ModularCurve.ModuliTestDatum.restrictLevel_gen ModularCurve.ModuliTestDatum.mk.sizeOf_spec ModularCurve.coe_jqNFull ModularCurve.qExpandAlgHomC_apply ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply"
p2m_attr_erase "simp" "WeierstrassCurve.mapPoint_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.multiGoal false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField

noncomputable section

namespace R1LevelHeckeUnits

section Places

abbrev pgen (w : HeightOneSpectrum (𝓞 ℚ)) : ℕ := Rat.HeightOneSpectrum.natGenerator w

theorem pgen_prime (w : HeightOneSpectrum (𝓞 ℚ)) : (pgen w).Prime :=
  Rat.HeightOneSpectrum.prime_natGenerator w

def place (p : ℕ) (hp : p.Prime) : HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hp⟩

theorem primesEquiv_place (p : ℕ) (hp : p.Prime) :
    Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) (place p hp) = ⟨p, hp⟩ := by
  simp [place]

theorem pgen_place (p : ℕ) (hp : p.Prime) : pgen (place p hp) = p :=
  congrArg Subtype.val (primesEquiv_place p hp)

theorem natCast_mem_asIdeal_iff (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    (n : 𝓞 ℚ) ∈ w.asIdeal ↔ pgen w ∣ n := by
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff,
    ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n, Ideal.apply_mem_of_equiv_iff]

theorem pgen_eq_of_prime_mem {p : ℕ} (hp : p.Prime) (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : (p : 𝓞 ℚ) ∈ v.asIdeal) : pgen v = p :=
  (Nat.prime_dvd_prime_iff_eq (pgen_prime v) hp).1 ((natCast_mem_asIdeal_iff v p).1 hv)

theorem pgen_injective : Function.Injective pgen := by
  intro w w' h
  apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective
  exact Subtype.ext h

theorem eq_place_of_mem {p : ℕ} (hp : p.Prime) (w : HeightOneSpectrum (𝓞 ℚ))
    (hw : (p : 𝓞 ℚ) ∈ w.asIdeal) : w = place p hp :=
  pgen_injective (by rw [pgen_eq_of_prime_mem hp w hw, pgen_place])

theorem natCast_mem_asIdeal_place (p : ℕ) (hp : p.Prime) : (p : 𝓞 ℚ) ∈ (place p hp).asIdeal :=
  (natCast_mem_asIdeal_iff _ _).2 (by rw [pgen_place])

theorem asIdeal_eq_span_pgen (w : HeightOneSpectrum (𝓞 ℚ)) :
    w.asIdeal = Ideal.span {((pgen w : ℕ) : 𝓞 ℚ)} := by
  set e := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)
  have h := Rat.HeightOneSpectrum.span_natGenerator (R := 𝓞 ℚ) w
  have h1 : w.asIdeal = (w.asIdeal.map e).comap e := (Ideal.comap_map_of_bijective e e.bijective).symm
  rw [h1, ← h, ← Ideal.map_symm, Ideal.map_span, Set.image_singleton]
  congr 2
  simp [e]

theorem valuation_pgen_self (w : HeightOneSpectrum (𝓞 ℚ)) :
    w.valuation ℚ ((pgen w : ℕ) : ℚ) = WithZero.exp (-1 : ℤ) := by
  rw [show ((pgen w : ℕ) : ℚ) = algebraMap (𝓞 ℚ) ℚ ((pgen w : ℕ) : 𝓞 ℚ) from (map_natCast _ _).symm,
    HeightOneSpectrum.valuation_of_algebraMap]
  refine HeightOneSpectrum.intValuation_singleton w ?_ (asIdeal_eq_span_pgen w)
  exact_mod_cast (pgen_prime w).ne_zero

theorem valued_algebraMap (w : HeightOneSpectrum (𝓞 ℚ)) (c : ℚ) :
    Valued.v (algebraMap ℚ (w.adicCompletion ℚ) c) = w.valuation ℚ c := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w c

theorem valuation_natCast_eq_one_of_not_dvd (w : HeightOneSpectrum (𝓞 ℚ)) {n : ℕ} (hn : ¬ pgen w ∣ n) :
    w.valuation ℚ (n : ℚ) = 1 := by
  rw [show (n : ℚ) = algebraMap (𝓞 ℚ) ℚ n from (map_natCast _ _).symm]
  refine (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := ℚ) (v := w) (r := (n : 𝓞 ℚ))).2 ?_
  rwa [natCast_mem_asIdeal_iff]

theorem valuation_natCast_lt_one_of_dvd (w : HeightOneSpectrum (𝓞 ℚ)) {n : ℕ} (hn : pgen w ∣ n) :
    w.valuation ℚ (n : ℚ) < 1 := by
  rw [show (n : ℚ) = algebraMap (𝓞 ℚ) ℚ n from (map_natCast _ _).symm,
    HeightOneSpectrum.valuation_of_algebraMap]
  exact (HeightOneSpectrum.intValuation_lt_one_iff_mem _ _).2 ((natCast_mem_asIdeal_iff _ _).2 hn)

theorem mem_integers_iff (w : HeightOneSpectrum (𝓞 ℚ)) (x : w.adicCompletion ℚ) :
    x ∈ w.adicCompletionIntegers ℚ ↔ Valued.v x ≤ 1 := HeightOneSpectrum.mem_adicCompletionIntegers _ _ _

theorem intCast_mem_integers (w : HeightOneSpectrum (𝓞 ℚ)) (t : ℤ) :
    (t : w.adicCompletion ℚ) ∈ w.adicCompletionIntegers ℚ := intCast_mem _ t

theorem natCast_mem_integers (w : HeightOneSpectrum (𝓞 ℚ)) (t : ℕ) :
    (t : w.adicCompletion ℚ) ∈ w.adicCompletionIntegers ℚ := natCast_mem _ t

theorem not_mem_asIdeal_of_prime_of_ne (w : HeightOneSpectrum (𝓞 ℚ)) {r q : ℕ} (hr : r.Prime) (hq : q.Prime)
    (hrq : r ≠ q) (hrw : (r : 𝓞 ℚ) ∈ w.asIdeal) : (q : 𝓞 ℚ) ∉ w.asIdeal := by
  intro hqw
  rw [natCast_mem_asIdeal_iff] at hrw hqw
  have h1 := (Nat.prime_dvd_prime_iff_eq (pgen_prime w) hr).mp hrw
  have h2 := (Nat.prime_dvd_prime_iff_eq (pgen_prime w) hq).mp hqw
  exact hrq (h1.symm.trans h2)

end Places

section Coord

variable {a b : ℚ}

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

abbrev cst (w : HeightOneSpectrum (𝓞 ℚ)) (q : ℚ) : w.adicCompletion ℚ := algebraMap ℚ (w.adicCompletion ℚ) q

def hatQ (w : HeightOneSpectrum (𝓞 ℚ)) (x : ℍ[ℚ, a, b]) : ℍ[w.adicCompletion ℚ, cst w a, cst w b] :=
  ⟨cst w x.re, cst w x.imI, cst w x.imJ, cst w x.imK⟩

theorem hatQ_star (w : HeightOneSpectrum (𝓞 ℚ)) (x : ℍ[ℚ, a, b]) : hatQ w (star x) = star (hatQ w x) := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  ext <;> simp [hatQ, map_neg]

theorem hatQ_one (w : HeightOneSpectrum (𝓞 ℚ)) : hatQ w (1 : ℍ[ℚ, a, b]) = 1 := by
  ext <;> simp [hatQ]

theorem hatQ_smul (w : HeightOneSpectrum (𝓞 ℚ)) (c : ℚ) (x : ℍ[ℚ, a, b]) :
    hatQ w (c • x) = cst w c • hatQ w x := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  ext <;> simp [hatQ, map_mul]

theorem nrd_hatQ (w : HeightOneSpectrum (𝓞 ℚ)) (x : ℍ[ℚ, a, b]) :
    QuaternionAlgebra.nrd (hatQ w x) = cst w (QuaternionAlgebra.nrd x) := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  simp [hatQ, QuaternionAlgebra.nrd, map_add, map_sub, map_mul, map_pow]

theorem trd_hatQ (w : HeightOneSpectrum (𝓞 ℚ)) (x : ℍ[ℚ, a, b]) :
    QuaternionAlgebra.trd (hatQ w x) = cst w (QuaternionAlgebra.trd x) := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  simp [hatQ, QuaternionAlgebra.trd, map_mul]

theorem nrd_mul' {K : Type*} [CommRing K] {c₁ c₃ : K} (x y : ℍ[K, c₁, c₃]) :
    QuaternionAlgebra.nrd (x * y) = QuaternionAlgebra.nrd x * QuaternionAlgebra.nrd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.nrd_mk]
  ring

theorem nrd_smul' {K : Type*} [CommRing K] {c₁ c₃ : K} (c : K) (x : ℍ[K, c₁, c₃]) :
    QuaternionAlgebra.nrd (c • x) = c ^ 2 * QuaternionAlgebra.nrd x := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  simp only [QuaternionAlgebra.smul_mk, QuaternionAlgebra.nrd_mk, smul_eq_mul]
  ring

theorem trd_smul' {K : Type*} [CommRing K] {c₁ c₃ : K} (c : K) (x : ℍ[K, c₁, c₃]) :
    QuaternionAlgebra.trd (c • x) = c * QuaternionAlgebra.trd x := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  simp only [QuaternionAlgebra.smul_mk, QuaternionAlgebra.trd_mk, smul_eq_mul]
  ring

theorem trd_add' {K : Type*} [CommRing K] {c₁ c₃ : K} (x y : ℍ[K, c₁, c₃]) :
    QuaternionAlgebra.trd (x + y) = QuaternionAlgebra.trd x + QuaternionAlgebra.trd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_add_mk, QuaternionAlgebra.trd_mk]
  ring

theorem trd_neg' {K : Type*} [CommRing K] {c₁ c₃ : K} (x : ℍ[K, c₁, c₃]) :
    QuaternionAlgebra.trd (-x) = -QuaternionAlgebra.trd x := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  simp [QuaternionAlgebra.trd]

theorem trd_zero' {K : Type*} [CommRing K] {c₁ c₃ : K} :
    QuaternionAlgebra.trd (0 : ℍ[K, c₁, c₃]) = 0 := by
  simp [QuaternionAlgebra.trd]

theorem nrd_add' {K : Type*} [CommRing K] {c₁ c₃ : K} (x y : ℍ[K, c₁, c₃]) :
    QuaternionAlgebra.nrd (x + y) =
      QuaternionAlgebra.nrd x + QuaternionAlgebra.nrd y + QuaternionAlgebra.trd (x * star y) := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_add_mk, QuaternionAlgebra.nrd_mk, QuaternionAlgebra.trd,
    QuaternionAlgebra.star_mk, QuaternionAlgebra.mk_mul_mk, zero_mul, add_zero]
  ring

theorem nrd_nonneg (ha : a < 0) (hb : b < 0) (x : ℍ[ℚ, a, b]) : 0 ≤ QuaternionAlgebra.nrd x := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  rw [QuaternionAlgebra.nrd_mk]
  have hab : 0 < a * b := mul_pos_of_neg_of_neg ha hb
  nlinarith [sq_nonneg x₀, sq_nonneg x₁, sq_nonneg x₂, sq_nonneg x₃, mul_pos_of_neg_of_neg ha hb]

def nrdHom (a b : ℚ) : ℍ[ℚ, a, b] →* ℚ where
  toFun := QuaternionAlgebra.nrd
  map_one' := QuaternionAlgebra.nrd_one
  map_mul' := nrd_mul'

theorem nrd_units_zpow (x : (ℍ[ℚ, a, b])ˣ) (n : ℤ) :
    QuaternionAlgebra.nrd ((x ^ n : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = QuaternionAlgebra.nrd (x : ℍ[ℚ, a, b]) ^ n := by
  have h := congrArg Units.val (map_zpow (Units.map (nrdHom a b)) x n)
  rw [Units.val_zpow_eq_zpow_val] at h
  exact h

theorem nrd_units_ne_zero (x : (ℍ[ℚ, a, b])ˣ) : QuaternionAlgebra.nrd (x : ℍ[ℚ, a, b]) ≠ 0 := by
  intro h
  have h1 : QuaternionAlgebra.nrd ((x⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * QuaternionAlgebra.nrd (x : ℍ[ℚ, a, b]) = 1 := by
    rw [← nrd_mul', ← Units.val_mul, inv_mul_cancel, Units.val_one, QuaternionAlgebra.nrd_one]
  rw [h, mul_zero] at h1
  exact zero_ne_one h1

def IsCoord (a b : ℚ) (w : HeightOneSpectrum (𝓞 ℚ))
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
      ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b]) : Prop :=
  ∀ (z : ℍ[ℚ, a, b]) (r : w.adicCompletion ℚ),
    φ (z ⊗ₜ[ℚ] r) = r • (⟨algebraMap ℚ (w.adicCompletion ℚ) z.re,
      algebraMap ℚ (w.adicCompletion ℚ) z.imI, algebraMap ℚ (w.adicCompletion ℚ) z.imJ,
      algebraMap ℚ (w.adicCompletion ℚ) z.imK⟩ :
        ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b])

theorem exists_isCoord (a b : ℚ) (w : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
      ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b],
      IsCoord a b w φ := by
  obtain ⟨φ, -, hφ⟩ := QuaternionAlgebra.exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
    (R := ℚ) (S := w.adicCompletion ℚ) (c₁ := a) (c₂ := (0 : ℚ)) (c₃ := b)
    (d₁ := algebraMap ℚ (w.adicCompletion ℚ) a) (d₂ := (0 : w.adicCompletion ℚ))
    (d₃ := algebraMap ℚ (w.adicCompletion ℚ) b) rfl (map_zero _) rfl AlgEquiv.refl
  exact ⟨φ, fun z r => by rw [hφ]; rfl⟩

def coord (a b : ℚ) (w : HeightOneSpectrum (𝓞 ℚ)) :
    ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
      ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b] :=
  Classical.choose (exists_isCoord a b w)

theorem isCoord_coord (a b : ℚ) (w : HeightOneSpectrum (𝓞 ℚ)) : IsCoord a b w (coord a b w) :=
  Classical.choose_spec (exists_isCoord a b w)

variable {w : HeightOneSpectrum (𝓞 ℚ)}
  {φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
    ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b]}

theorem IsCoord.tmul (hφ : IsCoord a b w φ) (z : ℍ[ℚ, a, b]) (r : w.adicCompletion ℚ) :
    φ (z ⊗ₜ[ℚ] r) = r • hatQ w z := by
  rw [hφ]; rfl

theorem IsCoord.tmul_one (hφ : IsCoord a b w φ) (z : ℍ[ℚ, a, b]) :
    φ (z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) = hatQ w z := by
  rw [hφ.tmul, one_smul]

theorem IsCoord.one_tmul (hφ : IsCoord a b w φ) (c : w.adicCompletion ℚ) :
    φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) = (c : ℍ[w.adicCompletion ℚ, cst w a, cst w b]) := by
  rw [hφ.tmul, hatQ_one]
  ext <;> simp

theorem IsCoord.symm_coe (hφ : IsCoord a b w φ) (c : w.adicCompletion ℚ) :
    φ.symm (c : ℍ[w.adicCompletion ℚ, cst w a, cst w b]) = (1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c := by
  rw [← hφ.one_tmul, RingEquiv.symm_apply_apply]

theorem isCoord_unique
    {φ' : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
      ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b]}
    (hφ : IsCoord a b w φ) (hφ' : IsCoord a b w φ') (x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) :
    φ x = φ' x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul z r => rw [hφ, hφ']
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem IsCoord.ratSmul (hφ : IsCoord a b w φ) (c : ℚ) (x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) :
    φ (c • x) = cst w c • φ x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul z r => rw [TensorProduct.smul_tmul', hφ.tmul, hφ.tmul, hatQ_smul, smul_comm]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

theorem nrd_φ_tmul_one (hφ : IsCoord a b w φ) (z : ℍ[ℚ, a, b]) :
    QuaternionAlgebra.nrd (φ (z ⊗ₜ[ℚ] 1)) = cst w (QuaternionAlgebra.nrd z) := by
  rw [hφ.tmul_one, nrd_hatQ]

def barT (φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
    ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b])
    (x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ :=
  φ.symm (star (φ x))

theorem φ_barT (x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) : φ (barT φ x) = star (φ x) := by
  rw [barT, RingEquiv.apply_symm_apply]

theorem barT_add (x x' : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) : barT φ (x + x') = barT φ x + barT φ x' := by
  apply φ.injective
  rw [RingEquiv.map_add, φ_barT, φ_barT, φ_barT, RingEquiv.map_add, star_add]

theorem barT_neg (x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) : barT φ (-x) = -barT φ x := by
  apply φ.injective
  rw [RingEquiv.map_neg, φ_barT, φ_barT, RingEquiv.map_neg, star_neg]

theorem barT_zero : barT φ (0 : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) = 0 := by
  apply φ.injective
  rw [φ_barT, RingEquiv.map_zero]
  exact star_zero _

theorem barT_tmul (hφ : IsCoord a b w φ) (z : ℍ[ℚ, a, b]) (c : w.adicCompletion ℚ) :
    barT φ (z ⊗ₜ[ℚ] c) = (star z) ⊗ₜ[ℚ] c := by
  apply φ.injective
  rw [φ_barT, hφ.tmul, hφ.tmul, hatQ_star]
  obtain ⟨z₀, z₁, z₂, z₃⟩ := z
  ext <;> simp [hatQ]

variable (a b)

def locNrd (w : HeightOneSpectrum (𝓞 ℚ))
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
      ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b])
    (x : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) : w.adicCompletion ℚ :=
  QuaternionAlgebra.nrd (φ (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w x))

variable {a b}

theorem locNrd_mul (x y : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) :
    locNrd a b w φ (x * y) = locNrd a b w φ x * locNrd a b w φ y := by
  simp only [locNrd, map_mul, nrd_mul']

theorem locNrd_one : locNrd a b w φ 1 = 1 := by
  simp only [locNrd, map_one, QuaternionAlgebra.nrd_one]

theorem locNrd_units_inv (x : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) :
    locNrd a b w φ ((x⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) *
      locNrd a b w φ (x : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) = 1 := by
  rw [← locNrd_mul, Units.inv_mul, locNrd_one]

theorem locNrd_units_inv_eq (x : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) :
    locNrd a b w φ ((x⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) =
      (locNrd a b w φ (x : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f))⁻¹ :=
  eq_inv_of_mul_eq_one_left (locNrd_units_inv x)

theorem locNrd_units_ne_zero (x : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) :
    locNrd a b w φ (x : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) ≠ 0 := by
  intro h
  have := locNrd_units_inv (φ := φ) x
  rw [h, mul_zero] at this
  exact zero_ne_one this

theorem locNrd_eq_of_isCoord
    {φ' : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
      ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b]}
    (hφ : IsCoord a b w φ) (hφ' : IsCoord a b w φ') (x : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) :
    locNrd a b w φ x = locNrd a b w φ' x := by
  simp only [locNrd, isCoord_unique hφ hφ']

theorem locNrd_diagonal (hφ : IsCoord a b w φ) (γ : ℍ[ℚ, a, b]) :
    locNrd a b w φ (γ ⊗ₜ[ℚ] (1 : 𝔸f)) = cst w (QuaternionAlgebra.nrd γ) := by
  simp only [locNrd, Submodule.finiteAdeleEvalAt_tmul]
  rw [show ((1 : 𝔸f) w) = (1 : w.adicCompletion ℚ) from rfl, nrd_φ_tmul_one hφ]

theorem locNrd_ratSmul (hφ : IsCoord a b w φ) (c : ℚ) (x : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) :
    locNrd a b w φ (c • x) = cst w c ^ 2 * locNrd a b w φ x := by
  simp only [locNrd, map_smul, hφ.ratSmul, nrd_smul']

end Coord

section Boxes

variable {a b : ℚ} {O : Submodule ℤ ℍ[ℚ, a, b]}

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

theorem tmul_mem_localBox {z : ℍ[ℚ, a, b]} (hz : z ∈ O) (w : HeightOneSpectrum (𝓞 ℚ))
    {c : w.adicCompletion ℚ} (hc : c ∈ w.adicCompletionIntegers ℚ) :
    z ⊗ₜ[ℚ] c ∈ Submodule.localBox O w :=
  AddSubgroup.subset_closure ⟨z, hz, c, hc, rfl⟩

theorem mul_mem_localBox (hO : QuaternionAlgebra.IsOrder O) (w : HeightOneSpectrum (𝓞 ℚ))
    {x y : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ}
    (hx : x ∈ Submodule.localBox O w) (hy : y ∈ Submodule.localBox O w) :
    x * y ∈ Submodule.localBox O w := by
  induction hy using AddSubgroup.closure_induction with
  | mem y' hy' =>
    obtain ⟨z', hz', c', hc', rfl⟩ := hy'
    induction hx using AddSubgroup.closure_induction with
    | mem x' hx' =>
      obtain ⟨z, hz, c, hc, rfl⟩ := hx'
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact tmul_mem_localBox (hO.mul_mem hz hz') w (Subring.mul_mem _ hc hc')
    | zero => rw [zero_mul]; exact AddSubgroup.zero_mem _
    | add u u' _ _ hu hu' => rw [add_mul]; exact AddSubgroup.add_mem _ hu hu'
    | neg u _ hu => rw [show -u * z' ⊗ₜ[ℚ] c' = -(u * z' ⊗ₜ[ℚ] c') from neg_mul u _]; exact AddSubgroup.neg_mem _ hu
  | zero => rw [mul_zero]; exact AddSubgroup.zero_mem _
  | add u u' _ _ hu hu' => rw [mul_add]; exact AddSubgroup.add_mem _ hu hu'
  | neg u _ hu => rw [show x * -u = -(x * u) from mul_neg x u]; exact AddSubgroup.neg_mem _ hu

theorem star_mem (hO : QuaternionAlgebra.IsOrder O) {z : ℍ[ℚ, a, b]} (hz : z ∈ O) : star z ∈ O := by
  obtain ⟨⟨t, n, ht, hn⟩, -⟩ := QuaternionAlgebra.IsOrder.exists_int_trd_eq_and_nrd_eq hO hz
  have e : star z = (t : ℤ) • (1 : ℍ[ℚ, a, b]) - z := by
    have h1 : z + star z = ((QuaternionAlgebra.trd z : ℚ) : ℍ[ℚ, a, b]) := QuaternionAlgebra.add_star_eq_coe_trd z
    rw [ht] at h1
    have : star z = ((t : ℚ) : ℍ[ℚ, a, b]) - z := by rw [← h1]; abel
    rw [this, ← Int.cast_smul_eq_zsmul ℚ]
    congr 1
    ext <;> simp
  rw [e]
  exact O.sub_mem (O.smul_mem _ hO.one_mem) hz

variable {w : HeightOneSpectrum (𝓞 ℚ)}
  {φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
    ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b]}

theorem barT_mem_localBox (hO : QuaternionAlgebra.IsOrder O) (hφ : IsCoord a b w φ)
    {x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ} (hx : x ∈ Submodule.localBox O w) :
    barT φ x ∈ Submodule.localBox O w := by
  induction hx using AddSubgroup.closure_induction with
  | mem x' hx' =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hx'
    rw [barT_tmul hφ]
    exact tmul_mem_localBox (star_mem hO hz) w hc
  | zero => rw [barT_zero]; exact AddSubgroup.zero_mem _
  | add u u' _ _ hu hu' => rw [barT_add]; exact AddSubgroup.add_mem _ hu hu'
  | neg u _ hu => rw [barT_neg]; exact AddSubgroup.neg_mem _ hu

theorem trd_mem_integers (hO : QuaternionAlgebra.IsOrder O) (hφ : IsCoord a b w φ)
    {x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ} (hx : x ∈ Submodule.localBox O w) :
    QuaternionAlgebra.trd (φ x) ∈ w.adicCompletionIntegers ℚ := by
  induction hx using AddSubgroup.closure_induction with
  | mem x' hx' =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hx'
    obtain ⟨⟨t, n, ht, hn⟩, -⟩ := QuaternionAlgebra.IsOrder.exists_int_trd_eq_and_nrd_eq hO hz
    rw [hφ.tmul, trd_smul', trd_hatQ, ht, show cst w (t : ℚ) = (t : w.adicCompletion ℚ) from map_intCast _ t]
    exact mul_mem hc (intCast_mem_integers w t)
  | zero => rw [RingEquiv.map_zero, trd_zero']; exact zero_mem _
  | add u u' _ _ hu hu' => rw [RingEquiv.map_add, trd_add']; exact add_mem hu hu'
  | neg u _ hu => rw [RingEquiv.map_neg, trd_neg']; exact neg_mem hu

theorem nrd_mem_integers (hO : QuaternionAlgebra.IsOrder O) (hφ : IsCoord a b w φ)
    {x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ} (hx : x ∈ Submodule.localBox O w) :
    QuaternionAlgebra.nrd (φ x) ∈ w.adicCompletionIntegers ℚ := by
  induction hx using AddSubgroup.closure_induction with
  | mem x' hx' =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hx'
    obtain ⟨⟨t, n, ht, hn⟩, -⟩ := QuaternionAlgebra.IsOrder.exists_int_trd_eq_and_nrd_eq hO hz
    rw [hφ.tmul, nrd_smul', nrd_hatQ, hn, show cst w (n : ℚ) = (n : w.adicCompletion ℚ) from map_intCast _ n]
    exact mul_mem (pow_mem hc 2) (intCast_mem_integers w n)
  | zero => rw [RingEquiv.map_zero, QuaternionAlgebra.nrd_zero]; exact zero_mem _
  | add u u' hu₀ hu'₀ hu hu' =>
    rw [RingEquiv.map_add, nrd_add', ← φ_barT, ← RingEquiv.map_mul]
    exact add_mem (add_mem hu hu')
      (trd_mem_integers hO hφ (mul_mem_localBox hO w hu₀ (barT_mem_localBox hO hφ hu'₀)))
  | neg u _ hu => rw [RingEquiv.map_neg, QuaternionAlgebra.nrd_neg]; exact hu

open QuaternionAlgebra CerednikDrinfeld

def boxUnits (hO : IsOrder O) (w : HeightOneSpectrum (𝓞 ℚ)) :
    Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ where
  carrier := Submodule.localBoxUnits O w
  one_mem' := by
    refine ⟨?_, ?_⟩
    · rw [Units.val_one, Algebra.TensorProduct.one_def]
      exact tmul_mem_localBox hO.one_mem w (one_mem _)
    · rw [inv_one, Units.val_one, Algebra.TensorProduct.one_def]
      exact tmul_mem_localBox hO.one_mem w (one_mem _)
  mul_mem' {x y} hx hy := by
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]; exact mul_mem_localBox hO w hx.1 hy.1
    · rw [mul_inv_rev, Units.val_mul]; exact mul_mem_localBox hO w hy.2 hx.2
  inv_mem' {x} hx := ⟨hx.2, by rw [inv_inv]; exact hx.1⟩

theorem mem_boxUnits_iff (hO : IsOrder O) (w : HeightOneSpectrum (𝓞 ℚ)) (u : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) :
    u ∈ boxUnits hO w ↔ u ∈ Submodule.localBoxUnits O w := Iff.rfl

theorem closure_localBoxUnits (hO : IsOrder O) (w : HeightOneSpectrum (𝓞 ℚ)) :
    Subgroup.closure (Submodule.localBoxUnits O w) = boxUnits hO w :=
  (boxUnits hO w).closure_eq

theorem toLoc_mem_boxUnits_of_mem_awayUnits (hO : IsOrder O) {v w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v)
    {γ : (ℍ[ℚ, a, b])ˣ} (hγ : γ ∈ CosetGraph.awayUnits O v) : CosetGraph.toLoc w γ ∈ boxUnits hO w := by
  have h := (Subgroup.mem_iInf.1 hγ) w
  rw [Subgroup.mem_iInf] at h
  have h' := h hw
  rwa [Subgroup.mem_comap, closure_localBoxUnits hO] at h'

theorem evalAt_mem_localBox_of_mem_box {x : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f} (hx : x ∈ Submodule.finiteAdeleBox O)
    (w : HeightOneSpectrum (𝓞 ℚ)) : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w x ∈ Submodule.localBox O w := by
  induction hx using AddSubgroup.closure_induction with
  | mem x' hx' =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hx'
    rw [Submodule.finiteAdeleEvalAt_tmul]
    exact tmul_mem_localBox hz w (hc w)
  | zero => rw [map_zero]; exact AddSubgroup.zero_mem _
  | add u u' _ _ hu hu' => rw [map_add]; exact AddSubgroup.add_mem _ hu hu'
  | neg u _ hu => rw [map_neg]; exact AddSubgroup.neg_mem _ hu

theorem one_mem_box (hO : IsOrder O) : (1 : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) ∈ Submodule.finiteAdeleBox O := by
  rw [Algebra.TensorProduct.one_def]
  exact AddSubgroup.subset_closure ⟨1, hO.one_mem, 1, fun v => one_mem _, rfl⟩

theorem val_mem_box_of_mem_stabilizer (hO : IsOrder O) {u : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ}
    (hu : u ∈ Submodule.finiteIdeleStabilizer O) : (u : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) ∈ Submodule.finiteAdeleBox O := by
  have hmem : (u : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) ∈
      u • ((Submodule.finiteAdeleBox O : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)) :=
    Set.mem_smul_set.mpr ⟨1, one_mem_box hO, by rw [Units.smul_def, smul_eq_mul, mul_one]⟩
  rwa [(Submodule.mem_finiteIdeleStabilizer_iff O u).mp hu] at hmem

theorem valued_nrd_eq_one_of_mem_localBoxUnits (hO : IsOrder O) (hφ : IsCoord a b w φ)
    {U : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ} (hU : U ∈ Submodule.localBoxUnits O w) :
    Valued.v (QuaternionAlgebra.nrd (φ (U : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ))) = 1 := by
  have h1 : Valued.v (QuaternionAlgebra.nrd (φ (U : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ))) ≤ 1 :=
    (mem_integers_iff _ _).1 (nrd_mem_integers hO hφ hU.1)
  have h2 : Valued.v (QuaternionAlgebra.nrd (φ ((U⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) :
      ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ))) ≤ 1 :=
    (mem_integers_iff _ _).1 (nrd_mem_integers hO hφ hU.2)
  have hprod : Valued.v (QuaternionAlgebra.nrd (φ ((U⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) :
      ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ))) *
      Valued.v (QuaternionAlgebra.nrd (φ (U : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ))) = 1 := by
    rw [← map_mul, ← nrd_mul', ← map_mul, Units.inv_mul, map_one, QuaternionAlgebra.nrd_one, map_one]
  refine le_antisymm h1 ?_
  calc (1 : WithZero (Multiplicative ℤ)) = _ := hprod.symm
    _ ≤ 1 * Valued.v (QuaternionAlgebra.nrd (φ (U : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ))) :=
        mul_le_mul_of_nonneg_right h2 zero_le'
    _ = _ := one_mul _

theorem inv_val_mem_localBox_of_valued_nrd_eq_one (hO : IsOrder O) (hφ : IsCoord a b w φ)
    (U : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ)
    (hU : (U : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) ∈ Submodule.localBox O w)
    (hv : Valued.v (QuaternionAlgebra.nrd (φ (U : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ))) = 1) :
    ((U⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) ∈ Submodule.localBox O w := by
  set x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ := (U : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) with hxdef
  set σ : w.adicCompletion ℚ := QuaternionAlgebra.nrd (φ x) with hσdef
  have hσ0 : σ ≠ 0 := fun h => by rw [h, map_zero] at hv; exact zero_ne_one hv
  have hσinv : σ⁻¹ ∈ w.adicCompletionIntegers ℚ := by
    rw [mem_integers_iff, map_inv₀, hv, inv_one]
  set x' : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ := ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] σ⁻¹) * barT φ x with hx'def
  have hx'x : x' * x = 1 := by
    apply φ.injective
    rw [map_mul, map_mul, hφ.one_tmul, φ_barT, map_one, mul_assoc, QuaternionAlgebra.star_mul_eq_coe_nrd,
      ← hσdef]
    ext <;> simp [hσ0]
  have hinv : ((U⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) = x' :=
    Units.inv_eq_of_mul_eq_one_left hx'x
  rw [hinv, hx'def]
  exact mul_mem_localBox hO w (tmul_mem_localBox hO.one_mem w hσinv) (barT_mem_localBox hO hφ hU)

end Boxes

section Trunc

variable {a b : ℚ}

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

open Classical in

def indAdele (v : HeightOneSpectrum (𝓞 ℚ)) : 𝔸f :=
  ⟨fun w => if w = v then 1 else 0, Filter.Eventually.of_forall fun w => by
    by_cases hw : w = v
    · simp only [hw, if_true]; exact one_mem _
    · simp only [hw, if_false]; exact zero_mem _⟩

open Classical in
theorem indAdele_apply (v w : HeightOneSpectrum (𝓞 ℚ)) :
    indAdele v w = if w = v then (1 : w.adicCompletion ℚ) else 0 := rfl

theorem indAdele_apply_self (v : HeightOneSpectrum (𝓞 ℚ)) : indAdele v v = 1 := by
  rw [indAdele_apply, if_pos rfl]

theorem indAdele_apply_of_ne {v w : HeightOneSpectrum (𝓞 ℚ)} (h : w ≠ v) : indAdele v w = 0 := by
  rw [indAdele_apply, if_neg h]

theorem indAdele_mul_self (v : HeightOneSpectrum (𝓞 ℚ)) : indAdele v * indAdele v = indAdele v := by
  refine FiniteAdeleRing.ext _ fun w => ?_
  show indAdele v w * indAdele v w = indAdele v w
  by_cases hw : w = v
  · subst hw; rw [indAdele_apply_self, mul_one]
  · rw [indAdele_apply_of_ne hw, mul_zero]

variable (a b) in

def idemE (v : HeightOneSpectrum (𝓞 ℚ)) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f := (1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] indAdele v

theorem idemE_mul_self (v : HeightOneSpectrum (𝓞 ℚ)) : idemE a b v * idemE a b v = idemE a b v := by
  rw [idemE, Algebra.TensorProduct.tmul_mul_tmul, mul_one, indAdele_mul_self]

theorem idemE_comm (v : HeightOneSpectrum (𝓞 ℚ)) (x : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) :
    idemE a b v * x = x * idemE a b v := by
  induction x using TensorProduct.induction_on with
  | zero => rw [mul_zero, zero_mul]
  | tmul z r => rw [idemE, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one,
      mul_comm]
  | add x y hx hy => rw [mul_add, add_mul, hx, hy]

variable (a b) in

def trunc (v : HeightOneSpectrum (𝓞 ℚ)) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f →* ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f where
  toFun x := x * (1 - idemE a b v) + idemE a b v
  map_one' := by rw [one_mul, sub_add_cancel]
  map_mul' x y := by
    set E := idemE a b v with hE
    have hEE : E * E = E := idemE_mul_self v
    have hEz : ∀ z : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f, E * z = z * E := idemE_comm v
    set F : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f := 1 - E with hFdef
    have hF : ∀ z : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f, F * z = z * F := fun z => by
      rw [hFdef, sub_mul, mul_sub, one_mul, mul_one, hEz z]
    have hFF : F * F = F := by
      rw [hFdef, sub_mul, one_mul, mul_sub, mul_one, hEE, sub_self, sub_zero]
    have hFE : F * E = 0 := by rw [hFdef, sub_mul, one_mul, hEE, sub_self]
    have hEF : E * F = 0 := by rw [hFdef, mul_sub, mul_one, hEE, sub_self]
    show x * y * F + E = (x * F + E) * (y * F + E)
    have h1 : x * F * (y * F) = x * y * F := by
      rw [mul_assoc x F, ← mul_assoc F y, hF y, mul_assoc y F F, hFF, ← mul_assoc x y F]
    have h2 : x * F * E = 0 := by rw [mul_assoc, hFE, mul_zero]
    have h3 : E * (y * F) = 0 := by rw [← mul_assoc, hEz y, mul_assoc, hEF, mul_zero]
    rw [add_mul, mul_add, mul_add, h1, h2, h3, hEE, add_zero, zero_add]

theorem trunc_apply (v : HeightOneSpectrum (𝓞 ℚ)) (x : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) :
    trunc a b v x = x * (1 - idemE a b v) + idemE a b v := rfl

theorem evalAt_idemE_self (v : HeightOneSpectrum (𝓞 ℚ)) :
    Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (idemE a b v) = 1 := by
  rw [idemE, Submodule.finiteAdeleEvalAt_tmul, indAdele_apply_self, Algebra.TensorProduct.one_def]

theorem evalAt_idemE_of_ne {v w : HeightOneSpectrum (𝓞 ℚ)} (h : w ≠ v) :
    Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (idemE a b v) = 0 := by
  rw [idemE, Submodule.finiteAdeleEvalAt_tmul, indAdele_apply_of_ne h, TensorProduct.tmul_zero]

theorem evalAt_trunc_self (v : HeightOneSpectrum (𝓞 ℚ)) (x : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) :
    Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (trunc a b v x) = 1 := by
  rw [trunc_apply, map_add, map_mul, map_sub, map_one, evalAt_idemE_self, sub_self, mul_zero, zero_add]

theorem evalAt_trunc_of_ne {v w : HeightOneSpectrum (𝓞 ℚ)} (h : w ≠ v) (x : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) :
    Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (trunc a b v x) = Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w x := by
  rw [trunc_apply, map_add, map_mul, map_sub, map_one, evalAt_idemE_of_ne h, sub_zero, mul_one, add_zero]

end Trunc

section Rational

theorem eq_one_of_forall_valuation_eq_one {t : ℚ} (ht : 0 < t)
    (h : ∀ w : HeightOneSpectrum (𝓞 ℚ), w.valuation ℚ t = 1) : t = 1 := by
  have hnum_pos : 0 < t.num := Rat.num_pos.2 ht
  have hnum : t.num = 1 := by
    have habs : t.num.natAbs = 1 := by
      by_contra hne
      obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd hne
      have hpd : ¬ p ∣ t.den := fun hpd => hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes t.reduced hpn hpd)
      have h1 : (place p hp).valuation ℚ ((t.num.natAbs : ℕ) : ℚ) < 1 :=
        valuation_natCast_lt_one_of_dvd _ (by rwa [pgen_place])
      have h2 : (place p hp).valuation ℚ ((t.den : ℕ) : ℚ) = 1 :=
        valuation_natCast_eq_one_of_not_dvd _ (by rwa [pgen_place])
      have ht' : t = ((t.num.natAbs : ℕ) : ℚ) / ((t.den : ℕ) : ℚ) := by
        rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (Int.cast_pos.2 hnum_pos)]
        exact (Rat.num_div_den t).symm
      have h3 := h (place p hp)
      rw [ht', map_div₀, h2, div_one] at h3
      exact h1.ne h3
    omega
  have hden : t.den = 1 := by
    by_contra hne
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
    have h1 : (place p hp).valuation ℚ ((t.den : ℕ) : ℚ) < 1 :=
      valuation_natCast_lt_one_of_dvd _ (by rwa [pgen_place])
    have ht' : t = 1 / ((t.den : ℕ) : ℚ) := by
      conv_lhs => rw [← Rat.num_div_den t, hnum, Int.cast_one]
    have h3 := h (place p hp)
    rw [ht', map_div₀, map_one] at h3
    have h4 : (place p hp).valuation ℚ ((t.den : ℕ) : ℚ) = 1 := by
      have := congrArg (fun z => z * (place p hp).valuation ℚ ((t.den : ℕ) : ℚ)) h3
      rw [one_mul, div_mul_cancel₀] at this
      · exact this.symm
      · exact (Valuation.ne_zero_iff _).2 (Nat.cast_ne_zero.2 t.den_ne_zero)
    exact h1.ne h4
  rw [← Rat.num_div_den t, hnum, hden]
  simp

theorem exists_eq_zpow_of_valuation_eq_one_off (v : HeightOneSpectrum (𝓞 ℚ)) {t : ℚ} (ht : 0 < t)
    (h : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → w.valuation ℚ t = 1) : ∃ j : ℤ, t = (pgen v : ℚ) ^ j := by
  have hp : (pgen v).Prime := pgen_prime v
  have hp0 : (pgen v : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hppos : (0 : ℚ) < (pgen v : ℚ) := by exact_mod_cast hp.pos
  have ht0 : t ≠ 0 := ht.ne'
  have hvt : v.valuation ℚ t ≠ 0 := (Valuation.ne_zero_iff _).2 ht0
  set j : ℤ := - WithZero.log (v.valuation ℚ t) with hj
  refine ⟨j, ?_⟩
  have key : t * (pgen v : ℚ) ^ (-j) = 1 := by
    apply eq_one_of_forall_valuation_eq_one (mul_pos ht (zpow_pos hppos _))
    intro w
    rw [map_mul, map_zpow₀]
    by_cases hw : w = v
    · subst hw
      rw [valuation_pgen_self, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one, neg_neg, hj,
        WithZero.exp_neg, WithZero.exp_log hvt, mul_inv_cancel₀ hvt]
    · rw [h w hw, valuation_natCast_eq_one_of_not_dvd w ?_, one_zpow, one_mul]
      intro hd
      exact hw (pgen_injective ((Nat.prime_dvd_prime_iff_eq (pgen_prime w) hp).1 hd))
  calc t = t * (pgen v : ℚ) ^ (-j) * (pgen v : ℚ) ^ j := by
        rw [mul_assoc, ← zpow_add₀ hp0, neg_add_cancel, zpow_zero, mul_one]
    _ = _ := by rw [key, one_mul]

end Rational

section StrongApprox

variable {a b : ℚ}

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

theorem eventually_algebraMap_mem_integers (r : ℚ) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite,
      algebraMap ℚ (w.adicCompletion ℚ) r ∈ w.adicCompletionIntegers ℚ :=
  (algebraMap ℚ 𝔸f r).2

theorem eventually_coords_mem_integers (x : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite,
      ∀ φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
        ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b],
        IsCoord a b w φ →
        (φ (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w x)).re ∈ w.adicCompletionIntegers ℚ ∧
        (φ (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w x)).imI ∈ w.adicCompletionIntegers ℚ ∧
        (φ (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w x)).imJ ∈ w.adicCompletionIntegers ℚ ∧
        (φ (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w x)).imK ∈ w.adicCompletionIntegers ℚ := by
  induction x using TensorProduct.induction_on with
  | zero =>
    refine Filter.Eventually.of_forall fun w φ hφ => ?_
    rw [map_zero, map_zero]
    exact ⟨zero_mem _, zero_mem _, zero_mem _, zero_mem _⟩
  | tmul z s =>
    filter_upwards [s.2, eventually_algebraMap_mem_integers z.re, eventually_algebraMap_mem_integers z.imI,
      eventually_algebraMap_mem_integers z.imJ, eventually_algebraMap_mem_integers z.imK]
      with w hs h0 h1 h2 h3
    intro φ hφ
    rw [Submodule.finiteAdeleEvalAt_tmul, hφ]
    exact ⟨mul_mem hs h0, mul_mem hs h1, mul_mem hs h2, mul_mem hs h3⟩
  | add x y hx hy =>
    filter_upwards [hx, hy] with w hx hy
    intro φ hφ
    obtain ⟨h0, h1, h2, h3⟩ := hx φ hφ
    obtain ⟨k0, k1, k2, k3⟩ := hy φ hφ
    rw [map_add, map_add]
    exact ⟨add_mem h0 k0, add_mem h1 k1, add_mem h2 k2, add_mem h3 k3⟩

theorem eventually_locNrd_mem_integers (x : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite,
      ∀ φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
        ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b],
        IsCoord a b w φ → locNrd a b w φ x ∈ w.adicCompletionIntegers ℚ := by
  filter_upwards [eventually_coords_mem_integers x, eventually_algebraMap_mem_integers a,
    eventually_algebraMap_mem_integers b] with w hx ha hb
  intro φ hφ
  obtain ⟨h0, h1, h2, h3⟩ := hx φ hφ
  simp only [locNrd, QuaternionAlgebra.nrd]
  refine add_mem (sub_mem (sub_mem (pow_mem h0 2) (mul_mem ha (pow_mem h1 2))) (mul_mem hb (pow_mem h2 2)))
    (mul_mem (mul_mem ha hb) (pow_mem h3 2))

theorem eventually_valued_locNrd_eq_one (x : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite,
      ∀ φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
        ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b],
        IsCoord a b w φ → Valued.v (locNrd a b w φ (x : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)) = 1 := by
  filter_upwards [eventually_locNrd_mem_integers (x : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f),
    eventually_locNrd_mem_integers ((x⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)] with w hx hxi
  intro φ hφ
  have h1 : Valued.v (locNrd a b w φ (x : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hx φ hφ)
  have h2 : Valued.v (locNrd a b w φ ((x⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hxi φ hφ)
  have hprod : Valued.v (locNrd a b w φ ((x⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)) *
      Valued.v (locNrd a b w φ (x : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)) = 1 := by
    rw [← map_mul, locNrd_units_inv, map_one]
  refine le_antisymm h1 ?_
  calc (1 : WithZero (Multiplicative ℤ))
        = Valued.v (locNrd a b w φ ((x⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)) *
          Valued.v (locNrd a b w φ (x : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)) := hprod.symm
    _ ≤ 1 * Valued.v (locNrd a b w φ (x : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)) := mul_le_mul_of_nonneg_right h2 zero_le'
    _ = _ := one_mul _

theorem exists_rat_valued_eq (n : (w : HeightOneSpectrum (𝓞 ℚ)) → w.adicCompletion ℚ)
    (hn0 : ∀ w, n w ≠ 0) (hn : ∀ᶠ w in Filter.cofinite, Valued.v (n w) = 1) :
    ∃ t : ℚ, 0 < t ∧ ∀ w : HeightOneSpectrum (𝓞 ℚ),
      Valued.v (algebraMap ℚ (w.adicCompletion ℚ) t) = Valued.v (n w) := by
  classical
  have hfin : {w : HeightOneSpectrum (𝓞 ℚ) | ¬ Valued.v (n w) = 1}.Finite := Filter.eventually_cofinite.1 hn
  set S : Finset (HeightOneSpectrum (𝓞 ℚ)) := hfin.toFinset with hS
  have hmemS : ∀ w, w ∈ S ↔ Valued.v (n w) ≠ 1 := fun w => by
    rw [hS, Set.Finite.mem_toFinset]; rfl
  let k : HeightOneSpectrum (𝓞 ℚ) → ℤ := fun w => WithZero.log (Valued.v (n w))
  have hk : ∀ w, WithZero.exp (k w) = Valued.v (n w) := fun w =>
    WithZero.exp_log ((Valuation.ne_zero_iff _).2 (hn0 w))
  let p : HeightOneSpectrum (𝓞 ℚ) → ℚ := fun w => ((pgen w : ℕ) : ℚ)
  have hp_pos : ∀ w, 0 < p w := fun w => by
    show (0 : ℚ) < ((pgen w : ℕ) : ℚ)
    exact_mod_cast (pgen_prime w).pos
  refine ⟨∏ w ∈ S, p w ^ (-(k w)), Finset.prod_pos fun w _ => zpow_pos (hp_pos w) _, fun w => ?_⟩
  rw [valued_algebraMap, map_prod]
  simp only [map_zpow₀]
  by_cases hw : w ∈ S
  · rw [Finset.prod_eq_single w]
    · rw [show p w = ((pgen w : ℕ) : ℚ) from rfl, valuation_pgen_self,
        ← WithZero.exp_zsmul, smul_neg, neg_smul, neg_neg, smul_eq_mul, mul_one, hk]
    · intro w' _ hw'
      rw [show p w' = ((pgen w' : ℕ) : ℚ) from rfl, valuation_natCast_eq_one_of_not_dvd w, one_zpow]
      intro hd
      exact hw' (pgen_injective ((Nat.prime_dvd_prime_iff_eq (pgen_prime w) (pgen_prime w')).1 hd)).symm
    · intro h; exact absurd hw h
  · rw [Finset.prod_eq_one]
    · have := (hmemS w).not.1 hw
      push Not at this
      exact this.symm
    · intro w' hw'
      have hne : w' ≠ w := fun h => hw (h ▸ hw')
      rw [show p w' = ((pgen w' : ℕ) : ℚ) from rfl, valuation_natCast_eq_one_of_not_dvd w, one_zpow]
      intro hd
      exact hne (pgen_injective ((Nat.prime_dvd_prime_iff_eq (pgen_prime w) (pgen_prime w')).1 hd)).symm

theorem strongApprox
    (q' : ℕ) [Fact q'.Prime] (hq'2 : q' ≠ 2) (hdef : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q')
    {N : ℕ} {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsEichlerOrder R N)
    (r : ℕ) (hr : r.Prime) (hrq' : r ≠ q')
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) :
    ∃ (γ : (ℍ[ℚ, a, b])ˣ) (g u : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ),
      u ∈ Submodule.finiteIdeleStabilizer R ∧
      (∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (g : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) = 1) ∧
      x = Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ * g * u := by
  classical
  have hq'P : q'.Prime := Fact.out

  let n : (w : HeightOneSpectrum (𝓞 ℚ)) → w.adicCompletion ℚ := fun w =>
    locNrd a b w (coord a b w) (x : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)
  have hn0 : ∀ w, n w ≠ 0 := fun w => locNrd_units_ne_zero x
  have hn1 : ∀ᶠ w in Filter.cofinite, Valued.v (n w) = 1 := by
    filter_upwards [eventually_valued_locNrd_eq_one x] with w hw
    exact hw _ (isCoord_coord a b w)
  obtain ⟨t, ht, hvt⟩ := exists_rat_valued_eq n hn0 hn1
  have ht0 : t ≠ 0 := ht.ne'
  have htw : ∀ w : HeightOneSpectrum (𝓞 ℚ), algebraMap ℚ (w.adicCompletion ℚ) t ≠ 0 := fun w => by
    simpa using (algebraMap ℚ (w.adicCompletion ℚ)).injective.ne ht0

  obtain ⟨γ₀, hγ₀⟩ := QuaternionAlgebra.IsDefiniteRamifiedExactlyAt.exists_nrd_eq_of_pos hq'2 hdef t ht
  have hγ₀inv : γ₀ * (t⁻¹ • star γ₀) = 1 := by
    rw [mul_smul_comm, QuaternionAlgebra.mul_star_eq_coe_nrd, hγ₀]
    ext <;> simp [ht0]
  have hγ₀inv' : (t⁻¹ • star γ₀) * γ₀ = 1 := by
    rw [smul_mul_assoc, QuaternionAlgebra.star_mul_eq_coe_nrd, hγ₀]
    ext <;> simp [ht0]
  let γ₀u : (ℍ[ℚ, a, b])ˣ := ⟨γ₀, t⁻¹ • star γ₀, hγ₀inv, hγ₀inv'⟩

  let ε : (w : HeightOneSpectrum (𝓞 ℚ)) → w.adicCompletion ℚ := fun w =>
    (algebraMap ℚ (w.adicCompletion ℚ) t)⁻¹ * n w
  have hε : ∀ w, Valued.v (ε w) = 1 := fun w => by
    simp only [ε, map_mul, map_inv₀, hvt w]
    exact inv_mul_cancel₀ ((Valuation.ne_zero_iff _).2 (hn0 w))
  obtain ⟨u₀, hu₀, hu₀n⟩ :=
    QuaternionAlgebra.IsEichlerOrder.exists_mem_finiteIdeleStabilizer_forall_nrd_eq hq'2 hdef hR ε hε

  set y : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ := (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ₀u)⁻¹ * x * u₀⁻¹ with hy_def
  have hy1 : ∀ w : HeightOneSpectrum (𝓞 ℚ),
      ∀ φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
        ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b],
        IsCoord a b w φ → locNrd a b w φ (y : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) = 1 := by
    intro w φ hφ
    have hdiag : locNrd a b w φ ((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ₀u : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) :
        ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) = algebraMap ℚ (w.adicCompletion ℚ) t := by
      rw [Submodule.val_finiteIdeleDiagonal_apply, locNrd_diagonal hφ]
      change algebraMap ℚ (w.adicCompletion ℚ) (QuaternionAlgebra.nrd γ₀) = _
      rw [hγ₀]
    have hdiag_inv : locNrd a b w φ (((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ₀u)⁻¹ :
        (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) = (algebraMap ℚ (w.adicCompletion ℚ) t)⁻¹ := by
      rw [locNrd_units_inv_eq, hdiag]
    have hu₀w : locNrd a b w φ (u₀ : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) = ε w := hu₀n w φ hφ
    have hu₀w_inv : locNrd a b w φ ((u₀⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) = (ε w)⁻¹ := by
      rw [locNrd_units_inv_eq, hu₀w]
    have hxw : locNrd a b w φ (x : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) = n w :=
      locNrd_eq_of_isCoord hφ (isCoord_coord a b w) _
    rw [hy_def, Units.val_mul, Units.val_mul, locNrd_mul, locNrd_mul, hdiag_inv, hxw, hu₀w_inv]
    simp only [ε]
    have key : (algebraMap ℚ (w.adicCompletion ℚ) t)⁻¹ *
        (n w * ((algebraMap ℚ (w.adicCompletion ℚ) t)⁻¹ * n w)⁻¹) = 1 := by
      rw [mul_inv, inv_inv, mul_comm (algebraMap ℚ (w.adicCompletion ℚ) t) (n w)⁻¹, ← mul_assoc (n w),
        mul_inv_cancel₀ (hn0 w), one_mul, inv_mul_cancel₀ (htw w)]
    rwa [mul_assoc]

  have hsplit : ∃ z : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, z ≠ 0 ∧ ¬ IsUnit z := by
    have hq'v : (q' : 𝓞 ℚ) ∉ v.asIdeal := not_mem_asIdeal_of_prime_of_ne v hr hq'P hrq' hv
    have h := (hdef.2.2 v).not.2 hq'v
    push Not at h
    exact h
  obtain ⟨β, g, u, hu, hg, hyeq⟩ :=
    QuaternionAlgebra.IsOrder.exists_eq_finiteIdeleDiagonal_mul_mul_of_forall_nrd_eq_one
      hdef.neg_left hdef.neg_right hR.isOrder v hsplit y (fun w hw φ hφ => hy1 w φ hφ)

  refine ⟨γ₀u * β, g, u * u₀, Subgroup.mul_mem _ hu hu₀, hg, ?_⟩
  have hx : x = Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ₀u * y * u₀ := by
    rw [hy_def]; group
  rw [hx, hyeq, map_mul]
  group

end StrongApprox

section Key

variable {a b : ℚ}

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

open QuaternionAlgebra CerednikDrinfeld

abbrev evU (a b : ℚ) (w : HeightOneSpectrum (𝓞 ℚ)) :
    (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ →* (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ :=
  Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w).toRingHom.toMonoidHom

theorem coe_evU (w : HeightOneSpectrum (𝓞 ℚ)) (y : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) :
    ((evU a b w y : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) =
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (y : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) :=
  rfl

theorem coe_evU_inv (w : HeightOneSpectrum (𝓞 ℚ)) (y : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) :
    (((evU a b w y)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) =
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((y⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) := by
  rw [← map_inv]; rfl

theorem evalAt_tmul_one (w : HeightOneSpectrum (𝓞 ℚ)) (z : ℍ[ℚ, a, b]) :
    Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (z ⊗ₜ[ℚ] (1 : 𝔸f)) = z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) := by
  rw [Submodule.finiteAdeleEvalAt_tmul]
  rfl

theorem coe_evU_diagonal (w : HeightOneSpectrum (𝓞 ℚ)) (x : (ℍ[ℚ, a, b])ˣ) :
    ((evU a b w (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] x) : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) :
        ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) = (x : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) := by
  rw [coe_evU, Submodule.val_finiteIdeleDiagonal_apply, evalAt_tmul_one]

theorem evU_diagonal_eq_toLoc (w : HeightOneSpectrum (𝓞 ℚ)) (x : (ℍ[ℚ, a, b])ˣ) :
    evU a b w (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] x) = CosetGraph.toLoc w x :=
  Units.ext (by rw [coe_evU_diagonal]; rfl)

theorem evU_eq_one_of_evalAt_eq_one {w : HeightOneSpectrum (𝓞 ℚ)} {y : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ}
    (h : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (y : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) = 1) : evU a b w y = 1 :=
  Units.ext (by rw [coe_evU, h, Units.val_one])

theorem ratSmul_one_eq_tmul (w : HeightOneSpectrum (𝓞 ℚ)) (c : ℚ) :
    (c • (1 : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)) = (1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] cst w c := by
  rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', TensorProduct.smul_tmul, Algebra.smul_def, mul_one]

theorem valued_locNrd_eq_of_mem_primeHeckeSet
    {S : Submodule ℤ ℍ[ℚ, a, b]} (hSo : IsOrder S) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (s₀ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ)
    (hs₀ : ∀ w : HeightOneSpectrum (𝓞 ℚ), ((ℓ : ℕ) : 𝓞 ℚ) ∉ w.asIdeal →
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (s₀ : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) = 1)
    (c : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) (hc : (c : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) = (ℓ : ℚ) • 1)
    (hh : c * s₀⁻¹ ∈ primeHeckeSet S ℓ) :
    Valued.v (locNrd a b (place ℓ hℓ) (coord a b (place ℓ hℓ)) (s₀ : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)) =
      WithZero.exp (-1 : ℤ) := by
  classical
  set vℓ := place ℓ hℓ with hvℓdef
  set φ := coord a b vℓ with hφdef
  have hφ : IsCoord a b vℓ φ := isCoord_coord a b vℓ
  have hℓ0 : (ℓ : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hℓ.ne_zero
  have hgen : pgen vℓ = ℓ := pgen_place ℓ hℓ
  have hℓvℓ : ((ℓ : ℕ) : 𝓞 ℚ) ∈ vℓ.asIdeal := natCast_mem_asIdeal_place ℓ hℓ
  have hcstℓ : Valued.v (cst vℓ (ℓ : ℚ)) = WithZero.exp (-1 : ℤ) := by
    rw [valued_algebraMap, ← hgen, valuation_pgen_self]

  have hcinv : ((c⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) = (ℓ : ℚ)⁻¹ • 1 := by
    have h1 : (c : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) * ((c⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) = 1 :=
      Units.mul_inv c
    rw [hc, smul_mul_assoc, one_mul] at h1
    calc ((c⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)
        = (ℓ : ℚ)⁻¹ • ((ℓ : ℚ) • ((c⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)) := by
          rw [smul_smul, inv_mul_cancel₀ hℓ0, one_smul]
      _ = _ := by rw [h1]
  have hval_h : ((c * s₀⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) =
      (ℓ : ℚ) • ((s₀⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) := by
    rw [Units.val_mul, hc, smul_mul_assoc, one_mul]
  have hval_hinv : (((c * s₀⁻¹)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) =
      (ℓ : ℚ)⁻¹ • (s₀ : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) := by
    rw [mul_inv_rev, inv_inv, Units.val_mul, hcinv, mul_smul_comm, mul_one]
  obtain ⟨hp1, hp2, hp3, hp4⟩ := hh
  rw [hval_h] at hp1
  rw [hval_hinv, smul_smul, mul_inv_cancel₀ hℓ0, one_smul] at hp2
  rw [hval_hinv] at hp3
  rw [hval_h, smul_smul, inv_mul_cancel₀ hℓ0, one_smul] at hp4

  set σ := locNrd a b vℓ φ (s₀ : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) with hσdef
  have hσ0 : σ ≠ 0 := locNrd_units_ne_zero s₀
  have hvσ0 : Valued.v σ ≠ 0 := (Valuation.ne_zero_iff _).2 hσ0
  have hσinv : locNrd a b vℓ φ ((s₀⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) = σ⁻¹ :=
    locNrd_units_inv_eq s₀

  have hσle : Valued.v σ ≤ 1 :=
    (mem_integers_iff _ _).1 (nrd_mem_integers hSo hφ (evalAt_mem_localBox_of_mem_box hp2 vℓ))
  have hσge' : Valued.v (cst vℓ (ℓ : ℚ) ^ 2 * σ⁻¹) ≤ 1 := by
    have h := nrd_mem_integers hSo hφ (evalAt_mem_localBox_of_mem_box hp1 vℓ)
    have h' : QuaternionAlgebra.nrd (φ (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] vℓ
        ((ℓ : ℚ) • ((s₀⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)))) = cst vℓ (ℓ : ℚ) ^ 2 * σ⁻¹ := by
      rw [← hσinv]; exact locNrd_ratSmul hφ (ℓ : ℚ) _
    rw [h'] at h
    exact (mem_integers_iff _ _).1 h
  have hσge : WithZero.exp (-2 : ℤ) ≤ Valued.v σ := by
    rw [map_mul, map_pow, hcstℓ, ← WithZero.exp_nsmul, map_inv₀] at hσge'
    have h2 : ((2 : ℕ) • (-1 : ℤ)) = -2 := by norm_num
    rw [h2, mul_inv_le_iff₀ (zero_lt_iff.2 hvσ0), one_mul] at hσge'
    exact hσge'

  have hne1 : Valued.v σ ≠ 1 := by
    intro hvσ
    apply hp4
    have hstab : s₀ ∈ Submodule.finiteIdeleStabilizer S := by
      rw [QuaternionAlgebra.IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits S hSo]
      intro w
      by_cases hw : w = vℓ
      · subst hw
        refine ⟨evalAt_mem_localBox_of_mem_box hp2 _, ?_⟩
        exact inv_val_mem_localBox_of_valued_nrd_eq_one hSo hφ _ (evalAt_mem_localBox_of_mem_box hp2 _) hvσ
      · have hℓw : ((ℓ : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := fun h => hw (eq_place_of_mem hℓ w h)
        have h1 : evU a b w s₀ = 1 := evU_eq_one_of_evalAt_eq_one (hs₀ w hℓw)
        rw [show Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w).toRingHom.toMonoidHom s₀ = evU a b w s₀
          from rfl, h1]
        exact (boxUnits hSo w).one_mem
    exact val_mem_box_of_mem_stabilizer hSo (inv_mem hstab)

  have hne2 : Valued.v σ ≠ WithZero.exp (-2 : ℤ) := by
    intro hvσ
    apply hp3
    have hstab : c * s₀⁻¹ ∈ Submodule.finiteIdeleStabilizer S := by
      rw [QuaternionAlgebra.IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits S hSo]
      intro w
      rw [show Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w).toRingHom.toMonoidHom (c * s₀⁻¹) =
        evU a b w (c * s₀⁻¹) from rfl]
      by_cases hw : w = vℓ
      · subst hw
        have hmem : ((evU a b vℓ (c * s₀⁻¹) : (ℍ[ℚ, a, b] ⊗[ℚ] vℓ.adicCompletion ℚ)ˣ) :
            ℍ[ℚ, a, b] ⊗[ℚ] vℓ.adicCompletion ℚ) ∈ Submodule.localBox S vℓ := by
          rw [coe_evU, hval_h]
          exact evalAt_mem_localBox_of_mem_box hp1 _
        refine ⟨hmem, inv_val_mem_localBox_of_valued_nrd_eq_one hSo hφ _ hmem ?_⟩
        rw [coe_evU, hval_h]
        have h' : QuaternionAlgebra.nrd (φ (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] vℓ
            ((ℓ : ℚ) • ((s₀⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)))) = cst vℓ (ℓ : ℚ) ^ 2 * σ⁻¹ := by
          rw [← hσinv]; exact locNrd_ratSmul hφ (ℓ : ℚ) _
        rw [h', map_mul, map_pow, hcstℓ, map_inv₀, hvσ, ← WithZero.exp_nsmul, ← WithZero.exp_neg,
          ← WithZero.exp_add]
        norm_num
      · have hℓw : ((ℓ : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := fun h => hw (eq_place_of_mem hℓ w h)
        have hℓw' : ¬ pgen w ∣ ℓ := fun h => hℓw ((natCast_mem_asIdeal_iff w ℓ).2 h)
        have h1 : evU a b w s₀ = 1 := evU_eq_one_of_evalAt_eq_one (hs₀ w hℓw)
        have h1' : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((s₀⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) :
            ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) = 1 := by
          rw [← coe_evU_inv, h1, inv_one, Units.val_one]
        refine ⟨?_, ?_⟩
        · rw [coe_evU, hval_h, map_smul, h1', ratSmul_one_eq_tmul,
            show cst w (ℓ : ℚ) = ((ℓ : ℕ) : w.adicCompletion ℚ) from map_natCast _ ℓ]
          exact tmul_mem_localBox hSo.one_mem w (natCast_mem_integers w ℓ)
        · rw [coe_evU_inv, hval_hinv, map_smul, hs₀ w hℓw, ratSmul_one_eq_tmul]
          refine tmul_mem_localBox hSo.one_mem w ?_
          rw [mem_integers_iff, valued_algebraMap, map_inv₀, valuation_natCast_eq_one_of_not_dvd w hℓw', inv_one]
    have := val_mem_box_of_mem_stabilizer hSo (inv_mem hstab)
    rwa [hval_hinv] at this

  set k : ℤ := WithZero.log (Valued.v σ) with hkdef
  have hk : Valued.v σ = WithZero.exp k := (WithZero.exp_log hvσ0).symm
  rw [hk] at hσle hσge hne1 hne2 ⊢
  rw [← WithZero.exp_zero, WithZero.exp_le_exp] at hσle
  rw [WithZero.exp_le_exp] at hσge
  rw [← WithZero.exp_zero, Ne, WithZero.exp_inj] at hne1
  rw [Ne, WithZero.exp_inj] at hne2
  rw [WithZero.exp_inj]
  omega

end Key

section Main

variable {a b : ℚ}

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

open QuaternionAlgebra CerednikDrinfeld

theorem main {N q q' : ℕ} [NeZero N] (hN : Squarefree N) [Fact q.Prime] [Fact q'.Prime]
    (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q) (hq'5 : 5 ≤ q')
    (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) (hn : n ∈ primeHeckeSet R q)
    (hS : IsEichlerOrder (meetOrder R n) (N * q))
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ∣ N) :
    ∃ (s : (ℍ[ℚ, a, b])ˣ) (sf : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ),
      (∀ w : HeightOneSpectrum (𝓞 ℚ), ((q : ℕ) : 𝓞 ℚ) ∉ w.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (sf : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) =
          (s : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) ∧
      (∀ w : HeightOneSpectrum (𝓞 ℚ), ((q : ℕ) : 𝓞 ℚ) ∈ w.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (sf : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) = 1) ∧
      Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]
          (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom
            (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))) * sf⁻¹ ∈
        levelHeckeUSet Λ (meetOrder R n) ℓ ∧
      QuaternionAlgebra.nrd (s : ℍ[ℚ, a, b]) = (ℓ : ℚ) := by
  classical
  have hqP : q.Prime := Fact.out
  have hq'P : q'.Prime := Fact.out
  have hℓP : ℓ.Prime := Fact.out
  have hq'2 : q' ≠ 2 := by omega
  have hqℓ : q ≠ ℓ := fun h => hqN (h ▸ hℓ)
  have hqq'' : q ≠ q' := fun h => hqq' h.symm
  have hℓ0 : (ℓ : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hℓP.ne_zero
  have hq0 : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hqP.ne_zero
  have ha : a < 0 := hdef.1
  have hb : b < 0 := hdef.2.1
  set S : Submodule ℤ ℍ[ℚ, a, b] := meetOrder R n with hSdef
  have hSo : IsOrder S := hS.isOrder
  have hSΛ : S ≤ Λ := le_trans (inf_le_left : R ⊓ Submodule.conjByFiniteIdele R n ≤ R) hRΛ

  set vq := place q hqP with hvqdef
  have hvq : ((q : ℕ) : 𝓞 ℚ) ∈ vq.asIdeal := natCast_mem_asIdeal_place q hqP
  have hgenq : pgen vq = q := pgen_place q hqP
  set vℓ := place ℓ hℓP with hvℓdef
  have hℓvq : ((ℓ : ℕ) : 𝓞 ℚ) ∉ vq.asIdeal := not_mem_asIdeal_of_prime_of_ne vq hqP hℓP hqℓ hvq

  obtain ⟨s₀, hs₀w, hs₀L, -⟩ :=
    CerednikDrinfeld.CSTower.exists_finiteIdeleDiagonal_mul_inv_mem_levelHeckeUSet_meetOrder_isEichlerOrder_of_dvd
      hN hqN hq'N hqq' hdef Λ R hΛ hR hRΛ n hn ℓ hℓ
  set c : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ := Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]
      (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom
        (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))) with hcdef
  have hcval : (c : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) = (ℓ : ℚ) • 1 := by
    rw [hcdef, Submodule.val_finiteIdeleDiagonal_apply, Units.coe_map, Units.val_mk0]
    change (algebraMap ℚ ℍ[ℚ, a, b] (ℓ : ℚ)) ⊗ₜ[ℚ] (1 : 𝔸f) = _
    rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul', Algebra.TensorProduct.one_def]
  have hccent : ∀ x : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ, x * c = c * x := fun x =>
    Units.ext (by rw [Units.val_mul, Units.val_mul, hcval, mul_smul_comm, smul_mul_assoc, mul_one, one_mul])

  haveI : NeZero (N * q) := ⟨mul_ne_zero (NeZero.ne N) hqP.ne_zero⟩
  have hNq : Squarefree (N * q) :=
    (Nat.squarefree_mul ((Nat.Prime.coprime_iff_not_dvd hqP).2 hqN).symm).2 ⟨hN, hqP.prime.squarefree⟩
  have hq'Nq : ¬ q' ∣ N * q := by
    intro h
    rcases (Nat.Prime.dvd_mul hq'P).1 h with h1 | h1
    · exact hq'N h1
    · exact hqq' ((Nat.prime_dvd_prime_iff_eq hq'P hqP).1 h1)
  have hL : levelHeckeUSet Λ S ℓ =
      DoubleCoset.doubleCoset (c * s₀⁻¹)
        (Submodule.finiteIdeleStabilizer S : Set (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ)
        (Submodule.finiteIdeleStabilizer S : Set (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) :=
    CerednikDrinfeld.levelHeckeUSet_eq_doubleCoset_finiteIdeleStabilizer_of_dvd_of_squarefree hdef hNq hS hΛ hSΛ
      hq'Nq ℓ (dvd_mul_of_dvd_left hℓ q) hs₀L

  obtain ⟨γ, g, u₁, hu₁, hg, hs₀eq⟩ := strongApprox q' hq'2 hdef hS q hqP hqq'' vq hvq s₀
  have hu₁loc := (QuaternionAlgebra.IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits
    S hSo u₁).1 hu₁
  set D := Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] with hD
  have hDγ : D γ = s₀ * u₁⁻¹ * g⁻¹ := by rw [hs₀eq]; group
  have hevγ : ∀ w, w ≠ vq → evU a b w (D γ) = evU a b w s₀ * (evU a b w u₁)⁻¹ := by
    intro w hw
    have hg1 : evU a b w g = 1 := evU_eq_one_of_evalAt_eq_one (hg w hw)
    rw [hDγ, map_mul, map_mul, map_inv, map_inv, hg1, inv_one, mul_one]

  have hkey := valued_locNrd_eq_of_mem_primeHeckeSet hSo hℓP s₀ hs₀w c hcval hs₀L.1
  have hval : ∀ w, w ≠ vq → w.valuation ℚ (QuaternionAlgebra.nrd (γ : ℍ[ℚ, a, b])) = w.valuation ℚ (ℓ : ℚ) := by
    intro w hw
    have hφ := isCoord_coord a b w

    have h1 := congrArg (fun U : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ =>
      Valued.v (QuaternionAlgebra.nrd (coord a b w (U : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)))) (hevγ w hw)
    rw [hD, coe_evU_diagonal, nrd_φ_tmul_one hφ, Units.val_mul, map_mul, nrd_mul', map_mul,
      valued_nrd_eq_one_of_mem_localBoxUnits hSo hφ ((boxUnits hSo w).inv_mem (hu₁loc w)), mul_one,
      valued_algebraMap] at h1
    rw [h1, coe_evU]
    change Valued.v (locNrd a b w (coord a b w) (s₀ : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)) = _
    by_cases hwℓ : w = vℓ
    · rw [hwℓ, hvℓdef, hkey, show ((ℓ : ℕ) : ℚ) = ((pgen (place ℓ hℓP) : ℕ) : ℚ) by rw [pgen_place],
        valuation_pgen_self]
    · have hℓw : ((ℓ : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := fun h => hwℓ (eq_place_of_mem hℓP w h)
      rw [locNrd, hs₀w w hℓw, map_one, QuaternionAlgebra.nrd_one, map_one, valuation_natCast_eq_one_of_not_dvd]
      exact fun hd => hℓw ((natCast_mem_asIdeal_iff w ℓ).2 hd)
  have hnrdγ_pos : 0 < QuaternionAlgebra.nrd (γ : ℍ[ℚ, a, b]) :=
    lt_of_le_of_ne (nrd_nonneg ha hb _) (nrd_units_ne_zero γ).symm
  obtain ⟨j, hj⟩ := exists_eq_zpow_of_valuation_eq_one_off vq
    (t := QuaternionAlgebra.nrd (γ : ℍ[ℚ, a, b]) / ℓ) (div_pos hnrdγ_pos (by exact_mod_cast hℓP.pos))
    (fun w hw => by
      rw [map_div₀, hval w hw, div_self]
      exact (Valuation.ne_zero_iff _).2 hℓ0)
  rw [hgenq] at hj
  have hnrdγ : QuaternionAlgebra.nrd (γ : ℍ[ℚ, a, b]) = ℓ * (q : ℚ) ^ j := by
    rw [← hj, mul_div_cancel₀ _ hℓ0]

  obtain ⟨δ, hδaway, hδn⟩ :=
    CerednikDrinfeld.CosetGraph.exists_mem_awayUnits_nrd_eq hq'2 hdef hS hqq'' vq hvq
  set s : (ℍ[ℚ, a, b])ˣ := γ * δ ^ (-j) with hsdef
  have hns : QuaternionAlgebra.nrd (s : ℍ[ℚ, a, b]) = ℓ := by
    rw [hsdef, Units.val_mul, nrd_mul', hnrdγ, nrd_units_zpow, hδn, mul_assoc, ← zpow_add₀ hq0, add_neg_cancel,
      zpow_zero, mul_one]

  set sf : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ := Units.map (trunc a b vq) (D s) with hsfdef
  have hsf_ne : ∀ w, w ≠ vq →
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (sf : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) = (s : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] 1 := by
    intro w hw
    rw [hsfdef, Units.coe_map, evalAt_trunc_of_ne hw, hD, Submodule.val_finiteIdeleDiagonal_apply,
      evalAt_tmul_one]
  have hsf_self : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] vq (sf : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) = 1 := by
    rw [hsfdef, Units.coe_map, evalAt_trunc_self]
  refine ⟨s, sf, fun w hw => hsf_ne w (fun h => hw (h ▸ hvq)), fun w hw => ?_, ?_, hns⟩
  · rw [eq_place_of_mem hqP w hw]
    exact hsf_self
  ·
    change c * sf⁻¹ ∈ levelHeckeUSet Λ S ℓ
    rw [hL, DoubleCoset.mem_doubleCoset]
    refine ⟨sf⁻¹ * s₀, ?_, 1, one_mem _, ?_⟩
    · rw [SetLike.mem_coe,
        QuaternionAlgebra.IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits S hSo]
      intro w
      rw [show Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w).toRingHom.toMonoidHom (sf⁻¹ * s₀) =
        evU a b w (sf⁻¹ * s₀) from rfl]
      by_cases hw : w = vq
      · subst hw
        have h1 : evU a b (place q hqP) sf = 1 := evU_eq_one_of_evalAt_eq_one hsf_self
        have h2 : evU a b (place q hqP) s₀ = 1 := evU_eq_one_of_evalAt_eq_one (hs₀w _ hℓvq)
        rw [map_mul, map_inv, h1, h2, inv_one, one_mul]
        exact (boxUnits hSo _).one_mem
      · have h1 : evU a b w sf = evU a b w (D s) :=
          Units.ext (by rw [coe_evU, coe_evU, hsf_ne w hw, hD, Submodule.val_finiteIdeleDiagonal_apply, evalAt_tmul_one])
        have hDs : D s = D γ * (D δ) ^ (-j) := by rw [hsdef, map_mul, map_zpow]
        have hδw : evU a b w (D δ) ∈ boxUnits hSo w := by
          rw [hD, evU_diagonal_eq_toLoc]
          exact toLoc_mem_boxUnits_of_mem_awayUnits hSo hw hδaway
        rw [map_mul, map_inv, h1, hDs, map_mul, map_zpow, hevγ w hw]
        have hgrp : (evU a b w s₀ * (evU a b w u₁)⁻¹ * evU a b w (D δ) ^ (-j))⁻¹ * evU a b w s₀ =
            evU a b w (D δ) ^ j * evU a b w u₁ := by group
        rw [hgrp]
        exact (boxUnits hSo w).mul_mem ((boxUnits hSo w).zpow_mem hδw j) (hu₁loc w)
    · calc c * sf⁻¹ = sf⁻¹ * c := (hccent _).symm
        _ = sf⁻¹ * (s₀ * (c * s₀⁻¹)) := by rw [← mul_assoc s₀, hccent s₀, mul_assoc, mul_inv_cancel, mul_one]
        _ = sf⁻¹ * s₀ * (c * s₀⁻¹) * 1 := by simp only [mul_assoc, mul_one]

end Main

end R1LevelHeckeUnits

end

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem solution
    {a b : ℚ} {N q q' : ℕ} [NeZero N] (hN : Squarefree N) [Fact q.Prime] [Fact q'.Prime]
    (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q) (hq'5 : 5 ≤ q')
    (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn : n ∈ primeHeckeSet R q)
    (hS : IsEichlerOrder (meetOrder R n) (N * q))
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ∣ N) :
    ∃ (s : (ℍ[ℚ, a, b])ˣ) (sf : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ),
      (∀ w : HeightOneSpectrum (𝓞 ℚ), ((q : ℕ) : 𝓞 ℚ) ∉ w.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (sf : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
          (s : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) ∧
      (∀ w : HeightOneSpectrum (𝓞 ℚ), ((q : ℕ) : 𝓞 ℚ) ∈ w.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (sf : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) ∧
      Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]
          (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom
            (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))) * sf⁻¹ ∈
        levelHeckeUSet Λ (meetOrder R n) ℓ ∧
      QuaternionAlgebra.nrd (s : ℍ[ℚ, a, b]) = (ℓ : ℚ) :=
  R1LevelHeckeUnits.main hN hqN hq'N hqq' hq'5 hdef Λ R hΛ hR hRΛ n hn hS ℓ hℓ

end S_CerednikDrinfeld_exists_units_finiteIdele_levelHeckeUSet_meetOrder_eq_tmul_one_of_dvd
end P2MW
export P2MW.S_CerednikDrinfeld_exists_units_finiteIdele_levelHeckeUSet_meetOrder_eq_tmul_one_of_dvd (solution)
