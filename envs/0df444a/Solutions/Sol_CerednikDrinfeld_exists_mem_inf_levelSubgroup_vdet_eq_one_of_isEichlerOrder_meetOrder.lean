-- Prove2me | solution 1 for CerednikDrinfeld.exists_mem_inf_levelSubgroup_vdet_eq_one_of_isEichlerOrder_meetOrder
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/56b8a4f0-0782-5d40-9b3f-d47eef7eade3

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_AlgFunctorConst
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_HeckeTower
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree

import Theorems.Thm_CerednikDrinfeld_CosetGraph_exists_mem_awayUnits_nrd_eq_of_le_isMaximalOrder
import Theorems.Thm_CerednikDrinfeld_awayUnits_exists_central_vdet_two_and_exists_vdet_one_and_exists_even
import Theorems.Thm_CerednikDrinfeld_CSTower_isEichlerOrder_meetOrder_of_finiteIdeleDiagonal_mul_inv_mem_primeHeckeSet_meetOrder
import Theorems.Thm_CerednikDrinfeld_CSTower_isEichlerOrder_meetOrder_of_finiteIdeleDiagonal_mul_inv_mem_levelHeckeUSet_meetOrder
import Theorems.Thm_CerednikDrinfeld_CosetGraph_mem_awayUnits_iff_conj_mem_awayUnits_of_conjByFiniteIdele_finiteIdeleDiagonal_mul_eq
import Theorems.Thm_QuaternionAlgebra_IsOrder_conjByFiniteIdele
import Theorems.Thm_CerednikDrinfeld_CosetGraph_awayUnits_mono
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_eq_of_natCast_prime_mem_asIdeal
import Theorems.Thm_Submodule_finiteAdeleEvalAt_finiteIdeleDiagonal_inv_mul_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_exists_mem_inf_levelSubgroup_vdet_eq_one_of_isEichlerOrder_meetOrder
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.SpecializationWitnessData.addCommGroup ModularCurve.CommutingHeckeFamily.commRing_adjoin ModularCurve.Gamma0Pair.isElliptic ModularCurve.ModuliTestDatum.isElliptic_reduced ModularCurve.ModuliTestDatum.isElliptic_curve ModularCurve.ModuliTestDatum.isElliptic_generic"
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val ModularCurve.coe_levelAlphaC ModularCurve.SSLevelDatum.mk.sizeOf_spec ModularCurve.SSLevelDatum.mk.injEq ModularCurve.coe_levelBetaC ModularCurve.coe_heckeBetaC AlgebraicCurve.Divisor.coe_degZeroEnd ModularCurve.coe_heckeAlphaC AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X"
p2m_attr_erase "simp" "ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.CommutingHeckeFamily.mk.injEq ModularCurve.SpecializationWitnessData.mk.sizeOf_spec ModularCurve.SpecializationWitnessData.mk.injEq ModularCurve.CommutingHeckeFamily.mk.sizeOf_spec ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk"
p2m_attr_erase "simp" "ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.ComapPlace.place_toValuationSubring ModularCurve.ModuliTestDatum.restrictLevel_emb ModularCurve.ModuliTestDatum.restrictLevel_res ModularCurve.ModuliTestDatum.mk.injEq ModularCurve.ModuliTestDatum.restrictLevel_W ModularCurve.ModuliTestDatum.place_toValuationSubring ModularCurve.ModuliTestDatum.restrictLevel_curve ModularCurve.ModuliTestDatum.resEquiv_apply ModularCurve.ModuliTestDatum.restrictLevel_gen ModularCurve.ModuliTestDatum.mk.sizeOf_spec ModularCurve.coe_jqNFull ModularCurve.qExpandAlgHomC_apply ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField MatrixGroups
open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.FormalOmega NeronModelInfra

theorem solution

    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (K₀ : Type) [Field K₀] [CharZero K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]

    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (vdet : Matrix.GeneralLinearGroup (Fin 2) K₀ →* Multiplicative ℤ)
    (hvdet : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℤ), vdet g = Multiplicative.ofAdd n ↔
      ∃ u : 𝒪ˣ, (Matrix.GeneralLinearGroup.det g : K₀) = algebraMap 𝒪 K₀ (u : 𝒪) * (algebraMap 𝒪 K₀ π) ^ n)

    {rbar N : ℕ} [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r)
    {a₁ b₁ : ℚ} (hdef : IsDefiniteRamifiedExactlyAt (a := a₁) (b := b₁) rbar)
    (hrN : ¬ r ∣ N) (hrbarN : ¬ rbar ∣ N) (hN : Squarefree N)
    (Λ₁ R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁ : IsMaximalOrder Λ₁) (hR₁ : IsEichlerOrder R₁ N) (hRΛ₁ : R₁ ≤ Λ₁)
    (ι₀ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) K₀) (hι₀ : Function.Injective ι₀)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (Γt : Subgroup (ℍ[ℚ, a₁, b₁])ˣ) (hΓt : ∀ x : (ℍ[ℚ, a₁, b₁])ˣ, x ∈ Γt ↔ x ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v)
    (n₁ : (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn₁ : n₁ ∈ primeHeckeSet R₁ r)
    (hS₁ : IsEichlerOrder (meetOrder R₁ n₁) (N * r))
    (s : HeckeTower.AwayPrime r rbar → (ℍ[ℚ, a₁, b₁])ˣ)
    (sf : HeckeTower.AwayPrime r rbar → (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hs : ∀ ℓ : HeckeTower.AwayPrime r rbar,
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((r : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] u (sf ℓ : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
          (s ℓ : ℍ[ℚ, a₁, b₁]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ)) ∧
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((r : ℕ) : 𝓞 ℚ) ∈ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] u (sf ℓ : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) ∧
      Submodule.finiteIdeleDiagonal ℍ[ℚ, a₁, b₁]
          (Units.map (algebraMap ℚ ℍ[ℚ, a₁, b₁]).toMonoidHom
            (Units.mk0 ((ℓ.1 : ℕ) : ℚ) (Nat.cast_ne_zero.mpr ℓ.1.prop.ne_zero))) * (sf ℓ)⁻¹ ∈
        (if (ℓ.1 : ℕ) ∣ N then levelHeckeUSet Λ₁ (meetOrder R₁ n₁) (ℓ.1 : ℕ)
          else primeHeckeSet (meetOrder R₁ n₁) (ℓ.1 : ℕ)) ∧
      nrd (s ℓ : ℍ[ℚ, a₁, b₁]) = ((ℓ.1 : ℕ) : ℚ))
    (Γtℓ : HeckeTower.AwayPrime r rbar → Subgroup (ℍ[ℚ, a₁, b₁])ˣ) (hΓtℓ : ∀ ℓ : HeckeTower.AwayPrime r rbar, Γtℓ ℓ = Γt ⊓ Γt.map (MulAut.conj (s ℓ)).toMonoidHom)
    (ℓ : HeckeTower.AwayPrime r rbar) :
    ∃ w ∈ Γt, w ∈ Γtℓ ℓ ∧
      vdet ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) w) = Multiplicative.ofAdd (1 : ℤ) := by
  classical
  haveI hℓP : Fact (ℓ.1 : ℕ).Prime := ⟨ℓ.1.prop⟩
  have hℓr : (ℓ.1 : ℕ) ≠ r := ℓ.2.1
  have hℓrbar : (ℓ.1 : ℕ) ≠ rbar := ℓ.2.2
  obtain ⟨hs1, hs2, hs3, hs4⟩ := hs ℓ

  set R' : Submodule ℤ ℍ[ℚ, a₁, b₁] := meetOrder R₁ (sf ℓ) with hR'def
  have hE' : IsEichlerOrder R' (N * (ℓ.1 : ℕ)) := by
    by_cases hℓN : (ℓ.1 : ℕ) ∣ N
    · rw [if_pos hℓN] at hs3
      exact CerednikDrinfeld.CSTower.isEichlerOrder_meetOrder_of_finiteIdeleDiagonal_mul_inv_mem_levelHeckeUSet_meetOrder
        hN hrN hrbarN hrr hdef Λ₁ R₁ hΛ₁ hR₁ hRΛ₁ n₁ hn₁ hS₁ (ℓ.1 : ℕ) hℓN (sf ℓ) hs3
    · rw [if_neg hℓN] at hs3
      have hℓ' : ¬ (ℓ.1 : ℕ) ∣ N * r * rbar := by
        intro h
        rcases (Nat.Prime.dvd_mul ℓ.1.prop).1 h with h1 | h1
        · rcases (Nat.Prime.dvd_mul ℓ.1.prop).1 h1 with h2 | h2
          · exact hℓN h2
          · exact hℓr ((Nat.prime_dvd_prime_iff_eq ℓ.1.prop (Fact.out)).1 h2)
        · exact hℓrbar ((Nat.prime_dvd_prime_iff_eq ℓ.1.prop (Fact.out)).1 h1)
      exact CerednikDrinfeld.CSTower.isEichlerOrder_meetOrder_of_finiteIdeleDiagonal_mul_inv_mem_primeHeckeSet_meetOrder
        hdef hR₁ n₁ hS₁ (ℓ.1 : ℕ) hℓ' (sf ℓ) hs3
  have hR'le : R' ≤ Λ₁ := inf_le_left.trans hRΛ₁
  haveI : NeZero (N * (ℓ.1 : ℕ)) := ⟨Nat.mul_ne_zero (NeZero.ne N) ℓ.1.prop.ne_zero⟩
  have hrNℓ : ¬ r ∣ N * (ℓ.1 : ℕ) := by
    intro h
    rcases (Nat.Prime.dvd_mul (Fact.out)).1 h with h1 | h1
    · exact hrN h1
    · exact hℓr ((Nat.prime_dvd_prime_iff_eq (Fact.out) ℓ.1.prop).1 h1).symm

  obtain ⟨wodd, hwodd, hwodd_nrd⟩ :=
    CerednikDrinfeld.CosetGraph.exists_mem_awayUnits_nrd_eq_of_le_isMaximalOrder hrr hrNℓ hdef Λ₁ R' hΛ₁ hE' hR'le v hv

  obtain ⟨-, ⟨w, hw, hwv⟩, -⟩ :=
    CerednikDrinfeld.awayUnits_exists_central_vdet_two_and_exists_vdet_one_and_exists_even 𝒪 hdvr π hπ hcomplete hres hunr K₀
      Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr vdet hvdet hrr hdef R' hE' ι₀ hι₀ v hv
      (CerednikDrinfeld.CosetGraph.awayUnits R' v) (fun _ => Iff.rfl) wodd hwodd hwodd_nrd

  have hw₁ : w ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v :=
    CerednikDrinfeld.CosetGraph.awayUnits_mono (inf_le_left : R' ≤ R₁) v hw
  have hw₂ : w ∈ CerednikDrinfeld.CosetGraph.awayUnits (Submodule.conjByFiniteIdele R₁ (sf ℓ)) v :=
    CerednikDrinfeld.CosetGraph.awayUnits_mono (inf_le_right : R' ≤ Submodule.conjByFiniteIdele R₁ (sf ℓ)) v hw

  set g : (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ := (Submodule.finiteIdeleDiagonal ℍ[ℚ, a₁, b₁] (s ℓ))⁻¹ * sf ℓ with hgdef
  have hg : ∀ w' : HeightOneSpectrum (𝓞 ℚ), w' ≠ v →
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] w' (g : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1 := by
    intro w' hw'
    have hrw' : ((r : ℕ) : 𝓞 ℚ) ∉ w'.asIdeal := fun h =>
      hw' (IsDedekindDomain.HeightOneSpectrum.eq_of_natCast_prime_mem_asIdeal (Fact.out) hv h)
    exact Submodule.finiteAdeleEvalAt_finiteIdeleDiagonal_inv_mul_eq_one w' (s ℓ) (sf ℓ) (hs1 w' hrw')
  have hconj : Submodule.conjByFiniteIdele R₁ (Submodule.finiteIdeleDiagonal ℍ[ℚ, a₁, b₁] (s ℓ) * g) =
      Submodule.conjByFiniteIdele R₁ (sf ℓ) := by
    rw [hgdef, ← mul_assoc, mul_inv_cancel, one_mul]
  have hconjOrd : IsOrder (Submodule.conjByFiniteIdele R₁ (sf ℓ)) :=
    QuaternionAlgebra.IsOrder.conjByFiniteIdele R₁ hR₁.isOrder (sf ℓ)
  have hw₃ : (s ℓ)⁻¹ * w * (s ℓ) ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v :=
    (CerednikDrinfeld.CosetGraph.mem_awayUnits_iff_conj_mem_awayUnits_of_conjByFiniteIdele_finiteIdeleDiagonal_mul_eq
      (Submodule.conjByFiniteIdele R₁ (sf ℓ)) R₁ hconjOrd hR₁.isOrder v (s ℓ) g hg hconj w).1 hw₂
  have hwmap : w ∈ Γt.map (MulAut.conj (s ℓ)).toMonoidHom := by
    refine ⟨(s ℓ)⁻¹ * w * (s ℓ), (hΓt _).2 hw₃, ?_⟩
    show (s ℓ) * ((s ℓ)⁻¹ * w * (s ℓ)) * (s ℓ)⁻¹ = w
    group
  refine ⟨w, (hΓt w).2 hw₁, ?_, hwv⟩
  rw [hΓtℓ ℓ]
  exact ⟨(hΓt w).2 hw₁, hwmap⟩

end S_CerednikDrinfeld_exists_mem_inf_levelSubgroup_vdet_eq_one_of_isEichlerOrder_meetOrder
end P2MW
export P2MW.S_CerednikDrinfeld_exists_mem_inf_levelSubgroup_vdet_eq_one_of_isEichlerOrder_meetOrder (solution)
