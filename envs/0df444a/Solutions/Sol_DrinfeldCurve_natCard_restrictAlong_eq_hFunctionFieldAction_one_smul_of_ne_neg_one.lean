-- Prove2me | solution 1 for DrinfeldCurve.natCard_restrictAlong_eq_hFunctionFieldAction_one_smul_of_ne_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/9d7ed7e7-5212-52cf-9868-989b8de06b0f

import Definitions.Def_DrinfeldCurve_FunctionField
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_JZeroTateModule
import Definitions.Def_AlgebraicCurve_Correspondence
import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Theorems.Thm_DrinfeldCurve_finite_and_ncard_setOf_twistedFrobenius_affineFixed
import Theorems.Thm_DrinfeldCurve_placesAtInfinity_census
import Theorems.Thm_DrinfeldCurve_isCurveOver_drinfeldFunctionField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DrinfeldCurve_natCard_restrictAlong_eq_hFunctionFieldAction_one_smul_of_ne_neg_one
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

noncomputable section

namespace DrinfeldCurve
p2m_export "DrinfeldCurve" "drinfeldFunctionField hFunctionFieldAction hFunctionFieldAction_mu CoordRing x y relation muAction muAction_x muAction_y one_mem_hSubgroup_of_mem finite_and_ncard_setOf_twistedFrobenius_affineFixed placesAtInfinity_census isCurveOver_drinfeldFunctionField"
p2m_open "DrinfeldCurve"

namespace CNTAux

open AlgebraicCurve IsLocalRing

section Nonunits

variable {F : Type*} [Field F]

theorem mem_nonunits_iff' (A : ValuationSubring F) (g : F) : g ∈ A.nonunits ↔ g = 0 ∨ g⁻¹ ∉ A := by
  rw [ValuationSubring.mem_nonunits_iff, ← ValuationSubring.valuation_le_one_iff, map_inv₀, not_le]
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  · rw [one_lt_inv₀ ((map_ne_zero _).mpr hg |>.bot_lt)]
    simp [hg]

theorem mem_nonunits_comap_iff {F' : Type*} [Field F'] (A : ValuationSubring F') (φ : F →+* F') (g : F) :
    g ∈ (A.comap φ).nonunits ↔ φ g ∈ A.nonunits := by
  rw [mem_nonunits_iff', mem_nonunits_iff', ValuationSubring.mem_comap, map_inv₀, map_eq_zero]

variable {K : Type*} [Field K] [Algebra K F]

open scoped Pointwise in

theorem mem_nonunits_smul_iff (σ : F ≃ₐ[K] F) (A : ValuationSubring F) (g : F) :
    g ∈ (σ • A).nonunits ↔ σ.symm g ∈ A.nonunits := by
  rw [mem_nonunits_iff', mem_nonunits_iff', ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def,
    map_inv₀, EmbeddingLike.map_eq_zero_iff]
  rfl

theorem mul_mem_nonunits (A : ValuationSubring F) {a g : F} (ha : a ∈ A) (hg : g ∈ A.nonunits) : a * g ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at hg ⊢
  rw [← ValuationSubring.valuation_le_one_iff] at ha
  calc A.valuation (a * g) = A.valuation a * A.valuation g := map_mul _ _ _
    _ ≤ 1 * A.valuation g := mul_le_mul_left ha _
    _ = A.valuation g := one_mul _
    _ < 1 := hg

theorem pow_mem_nonunits (A : ValuationSubring F) {g : F} (hg : g ∈ A.nonunits) {n : ℕ} (hn : n ≠ 0) : g ^ n ∈ A.nonunits := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [pow_succ]
  have hgA : g ∈ A := A.nonunits_le hg
  exact mul_mem_nonunits A (pow_mem hgA m) hg

theorem sub_mem_nonunits (A : ValuationSubring F) {g g' : F} (hg : g ∈ A.nonunits) (hg' : g' ∈ A.nonunits) : g - g' ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at hg hg' ⊢
  exact lt_of_le_of_lt (A.valuation.map_sub g g') (max_lt hg hg')

end Nonunits

section Values

variable {k F : Type*} [Field k] [Field F] [Algebra k F] (v : Place k F)

def HasVal (f : F) (c : k) : Prop := f - algebraMap k F c ∈ v.toValuationSubring.nonunits

variable {v}

theorem HasVal.mem {f : F} {c : k} (h : HasVal v f c) : f ∈ v.toValuationSubring := by
  have := add_mem (v.toValuationSubring.nonunits_le h) (v.algebraMap_mem' c)
  rwa [sub_add_cancel] at this

theorem HasVal.unique {f : F} {c c' : k} (h : HasVal v f c) (h' : HasVal v f c') : c = c' := by
  by_contra hne
  have hd : algebraMap k F (c' - c) ∈ v.toValuationSubring.nonunits := by
    have := sub_mem_nonunits _ h h'
    rwa [sub_sub_sub_cancel_left, ← map_sub] at this
  rw [mem_nonunits_iff', map_eq_zero, sub_eq_zero, ← map_inv₀] at hd
  rcases hd with hd | hd
  · exact hne hd.symm
  · exact hd (v.algebraMap_mem' _)

theorem hasVal_iff_residue {f : F} (hf : f ∈ v.toValuationSubring) (c : k) :
    HasVal v f c ↔ residue v.toValuationSubring ⟨f, hf⟩ = algebraMap k v.ResidueField c := by
  rw [HasVal]
  have hmem : f - algebraMap k F c ∈ v.toValuationSubring := sub_mem hf (v.algebraMap_mem' c)
  rw [show f - algebraMap k F c = ((⟨f - algebraMap k F c, hmem⟩ : v.toValuationSubring) : F) from rfl,
    ValuationSubring.coe_mem_nonunits_iff, ← residue_eq_zero_iff]
  have : (⟨f - algebraMap k F c, hmem⟩ : v.toValuationSubring) = ⟨f, hf⟩ - algebraMap k v.toValuationSubring c := by
    apply Subtype.ext; simp [Place.coe_algebraMap]
  rw [this, map_sub, sub_eq_zero, IsScalarTower.algebraMap_apply k v.toValuationSubring v.ResidueField c,
    IsLocalRing.ResidueField.algebraMap_eq]

theorem exists_hasVal (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) : ∃ c : k, HasVal v f c :=
  ⟨v.evalAt f, (hasVal_iff_residue hf _).mpr (v.algebraMap_evalAt hv hf).symm⟩

theorem hasVal_algebraMap (c : k) : HasVal v (algebraMap k F c) c := by
  rw [HasVal, sub_self]
  exact (mem_nonunits_iff' _ _).mpr (Or.inl rfl)

theorem HasVal.mul {f g : F} {c d : k} (hf : HasVal v f c) (hg : HasVal v g d) : HasVal v (f * g) (c * d) := by
  have hfm := hf.mem
  have hgm := hg.mem
  rw [hasVal_iff_residue hfm] at hf
  rw [hasVal_iff_residue hgm] at hg
  rw [hasVal_iff_residue (mul_mem hfm hgm)]
  have : (⟨f * g, mul_mem hfm hgm⟩ : v.toValuationSubring) = ⟨f, hfm⟩ * ⟨g, hgm⟩ := rfl
  rw [this, map_mul, hf, hg, ← map_mul]

theorem HasVal.pow {f : F} {c : k} (hf : HasVal v f c) (n : ℕ) : HasVal v (f ^ n) (c ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, ← (algebraMap k F).map_one]; exact hasVal_algebraMap 1
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul hf

theorem HasVal.sub {f g : F} {c d : k} (hf : HasVal v f c) (hg : HasVal v g d) : HasVal v (f - g) (c - d) := by
  have := sub_mem_nonunits _ hf hg
  rw [HasVal, map_sub]
  convert this using 1
  ring

theorem HasVal.const_mul (e : k) {f : F} {c : k} (hf : HasVal v f c) : HasVal v (algebraMap k F e * f) (e * c) :=
  (hasVal_algebraMap e).mul hf

theorem HasVal.eq_one_of_eq_one {f : F} {c : k} (hf : HasVal v f c) (h1 : f = 1) : c = 1 := by
  apply hf.unique
  rw [h1, ← (algebraMap k F).map_one]
  exact hasVal_algebraMap 1

end Values

section Transport

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

theorem hasVal_restrictAlong_iff (φ : F →ₐ[k] F) (hφ : φ.toRingHom.IsIntegral) (w : Place k F) (f : F) (c : k) :
    HasVal (w.restrictAlong φ hφ) f c ↔ HasVal w (φ f) c := by
  rw [HasVal, HasVal]
  have : (w.restrictAlong φ hφ).toValuationSubring = w.toValuationSubring.comap φ.toRingHom := rfl
  rw [this, mem_nonunits_comap_iff]
  simp

theorem hasVal_smul_iff (σ : F ≃ₐ[k] F) (w : Place k F) (f : F) (c : k) :
    HasVal (σ • w) f c ↔ HasVal w (σ.symm f) c := by
  rw [HasVal, HasVal, Place.smul_toValuationSubring, mem_nonunits_smul_iff, map_sub, AlgEquiv.commutes]

end Transport

section Drinfeld

variable (q : ℕ) [hq : Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsDomain (CoordRing q k)]

theorem charP_k : CharP k q := charP_of_injective_algebraMap' (GaloisField q 2) q

theorem charP_F : CharP (drinfeldFunctionField q k) q := by
  haveI := charP_k q k
  exact charP_of_injective_algebraMap (algebraMap k (drinfeldFunctionField q k)).injective q

abbrev xF : drinfeldFunctionField q k := algebraMap (CoordRing q k) (drinfeldFunctionField q k) (x q k)
abbrev yF : drinfeldFunctionField q k := algebraMap (CoordRing q k) (drinfeldFunctionField q k) (y q k)

theorem relF : xF q k * yF q k ^ q - xF q k ^ q * yF q k = 1 := by
  have h := congrArg (algebraMap (CoordRing q k) (drinfeldFunctionField q k)) (relation q k)
  simpa only [map_sub, map_mul, map_pow, map_one] using h

variable (η : rootsOfUnity (q + 1) (GaloisField q 2))

abbrev ση : drinfeldFunctionField q k ≃ₐ[k] drinfeldFunctionField q k :=
  hFunctionFieldAction q k ⟨_, one_mem_hSubgroup_of_mem q η⟩

abbrev ηk : k := algebraMap (GaloisField q 2) k ((η : (GaloisField q 2)ˣ) : GaloisField q 2)

theorem ηk_ne_zero : ηk q k η ≠ 0 := by
  rw [ηk, map_ne_zero]; exact Units.ne_zero _

theorem ση_eq : ση q k η = IsFractionRing.algEquivOfAlgEquiv (muAction q k η) := hFunctionFieldAction_mu q k η

theorem ση_xF : ση q k η (xF q k) = algebraMap k _ (ηk q k η) * xF q k := by
  rw [ση_eq, xF, IsFractionRing.algEquivOfAlgEquiv_algebraMap, muAction_x, map_mul, ← IsScalarTower.algebraMap_apply]
  rfl

theorem ση_yF : ση q k η (yF q k) = algebraMap k _ (ηk q k η) * yF q k := by
  rw [ση_eq, yF, IsFractionRing.algEquivOfAlgEquiv_algebraMap, muAction_y, map_mul, ← IsScalarTower.algebraMap_apply]
  rfl

theorem ση_symm_xF : (ση q k η).symm (xF q k) = algebraMap k _ (ηk q k η)⁻¹ * xF q k := by
  rw [AlgEquiv.symm_apply_eq, map_mul, AlgEquiv.commutes, ση_xF, ← mul_assoc, ← map_mul, inv_mul_cancel₀ (ηk_ne_zero q k η),
    map_one, one_mul]

theorem ση_symm_yF : (ση q k η).symm (yF q k) = algebraMap k _ (ηk q k η)⁻¹ * yF q k := by
  rw [AlgEquiv.symm_apply_eq, map_mul, AlgEquiv.commutes, ση_yF, ← mul_assoc, ← map_mul, inv_mul_cancel₀ (ηk_ne_zero q k η),
    map_one, one_mul]

variable (φ : drinfeldFunctionField q k →ₐ[k] drinfeldFunctionField q k) (hφi : φ.toRingHom.IsIntegral)

theorem value_transport {w : Place k (drinfeldFunctionField q k)} (hrel : w.restrictAlong φ hφi = ση q k η • w)
    {f : drinfeldFunctionField q k} {c : k} (hf : HasVal w f c) (hφf : φ f = f ^ q ^ 2)
    (hσf : (ση q k η).symm f = algebraMap k _ (ηk q k η)⁻¹ * f) : ηk q k η * c ^ q ^ 2 = c := by
  haveI := charP_k q k
  haveI := charP_F q k

  have h1 : HasVal (w.restrictAlong φ hφi) f (c ^ q ^ 2) := by
    rw [hasVal_restrictAlong_iff, hφf]
    exact hf.pow _

  have h2 : HasVal (w.restrictAlong φ hφi) f ((ηk q k η)⁻¹ * c) := by
    rw [hrel, hasVal_smul_iff, hσf]
    exact hf.const_mul _
  have h := h1.unique h2
  rw [h, ← mul_assoc, mul_inv_cancel₀ (ηk_ne_zero q k η), one_mul]

theorem values_mem_affineFixed (hφx : φ (xF q k) = xF q k ^ q ^ 2) (hφy : φ (yF q k) = yF q k ^ q ^ 2)
    {w : Place k (drinfeldFunctionField q k)} (hw : w.IsRational)
    (hx : xF q k ∈ w.toValuationSubring) (hy : yF q k ∈ w.toValuationSubring)
    (hrel : w.restrictAlong φ hφi = ση q k η • w) :
    ∃ a b : k, HasVal w (xF q k) a ∧ HasVal w (yF q k) b ∧
      a * b ^ q - a ^ q * b = 1 ∧ ηk q k η * a ^ q ^ 2 = a ∧ ηk q k η * b ^ q ^ 2 = b := by
  obtain ⟨a, ha⟩ := exists_hasVal hw hx
  obtain ⟨b, hb⟩ := exists_hasVal hw hy
  refine ⟨a, b, ha, hb, ?_, ?_, ?_⟩
  · exact ((ha.mul (hb.pow q)).sub ((ha.pow q).mul hb)).eq_one_of_eq_one (relF q k)
  · exact value_transport q k η φ hφi hrel ha hφx (ση_symm_xF q k η)
  · exact value_transport q k η φ hφi hrel hb hφy (ση_symm_yF q k η)

end Drinfeld

end CNTAux

namespace CNTAux

open AlgebraicCurve

section InfTransport

variable (q : ℕ) [hq : Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsAlgClosed k] [IsDomain (CoordRing q k)]
  (φ : drinfeldFunctionField q k →ₐ[k] drinfeldFunctionField q k) (hφi : φ.toRingHom.IsIntegral)
  (η : rootsOfUnity (q + 1) (GaloisField q 2))

abbrev UF : drinfeldFunctionField q k := xF q k / yF q k

theorem pow_mem_iff (A : ValuationSubring (drinfeldFunctionField q k)) (g : drinfeldFunctionField q k) {n : ℕ} (hn : n ≠ 0) :
    g ^ n ∈ A ↔ g ∈ A := by
  rw [← A.valuation_le_one_iff, ← A.valuation_le_one_iff, map_pow]
  exact pow_le_one_iff hn

theorem mem_restrictAlong_iff (w : Place k (drinfeldFunctionField q k)) (g : drinfeldFunctionField q k) :
    g ∈ (w.restrictAlong φ hφi).toValuationSubring ↔ φ g ∈ w.toValuationSubring := Iff.rfl

theorem mem_smul_place_iff (σ : drinfeldFunctionField q k ≃ₐ[k] drinfeldFunctionField q k) (w : Place k (drinfeldFunctionField q k))
    (g : drinfeldFunctionField q k) : g ∈ (σ • w).toValuationSubring ↔ σ.symm g ∈ w.toValuationSubring := by
  rw [Place.smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

theorem ord_smul_place (σ : drinfeldFunctionField q k ≃ₐ[k] drinfeldFunctionField q k) (w : Place k (drinfeldFunctionField q k))
    (g : drinfeldFunctionField q k) : (σ • w).ord g = w.ord (σ.symm g) := by
  conv_lhs => rw [← σ.apply_symm_apply g]
  exact Place.ord_smul σ w _

theorem ord_restrictAlong_pos_iff (w : Place k (drinfeldFunctionField q k)) (g : drinfeldFunctionField q k) :
    0 < (w.restrictAlong φ hφi).ord g ↔ 0 < w.ord (φ g) := by
  rw [Place.ord_restrictAlong φ hφi w g]
  have he : 0 < (Place.ramificationIndexAlong φ w : ℤ) := by
    letI := algebraAlong φ
    haveI := isScalarTower_along φ
    haveI := isIntegral_along φ hφi
    exact_mod_cast w.ramificationIndex_pos (F := drinfeldFunctionField q k)
  rw [mul_pos_iff_of_pos_left he]

theorem ord_pow_nat (w : Place k (drinfeldFunctionField q k)) (g : drinfeldFunctionField q k) (n : ℕ) :
    w.ord (g ^ n) = n * w.ord g := by
  rw [← zpow_natCast, Place.ord_zpow]

theorem ση_symm_UF : (ση q k η).symm (UF q k) = UF q k := by
  rw [UF, map_div₀, ση_symm_xF, ση_symm_yF, mul_div_mul_left]
  rw [map_ne_zero]
  exact inv_ne_zero (ηk_ne_zero q k η)

theorem UF_not_mem_smul_iff (w : Place k (drinfeldFunctionField q k)) :
    UF q k ∉ (ση q k η • w).toValuationSubring ↔ UF q k ∉ w.toValuationSubring := by
  rw [mem_smul_place_iff, ση_symm_UF]

theorem ord_UF_sub_pos_smul_iff (w : Place k (drinfeldFunctionField q k)) (a : k) :
    0 < (ση q k η • w).ord (UF q k - algebraMap k _ a) ↔ 0 < w.ord (UF q k - algebraMap k _ a) := by
  rw [ord_smul_place, map_sub, ση_symm_UF, AlgEquiv.commutes]

theorem isRational (w : Place k (drinfeldFunctionField q k)) : w.IsRational := by
  haveI : IsCurveOver k (drinfeldFunctionField q k) := isCurveOver_drinfeldFunctionField q k
  haveI : Module.Finite k w.ResidueField := IsCurveOver.finiteResidue w
  haveI : Algebra.IsIntegral k w.ResidueField := Algebra.IsIntegral.of_finite k _
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := w.ResidueField)).2

variable (hφx : φ (xF q k) = xF q k ^ q ^ 2) (hφy : φ (yF q k) = yF q k ^ q ^ 2)

include hφx hφy

theorem φ_UF : φ (UF q k) = UF q k ^ q ^ 2 := by
  rw [UF, map_div₀, hφx, hφy, div_pow]

theorem UF_not_mem_restrictAlong_iff (w : Place k (drinfeldFunctionField q k)) :
    UF q k ∉ (w.restrictAlong φ hφi).toValuationSubring ↔ UF q k ∉ w.toValuationSubring := by
  rw [mem_restrictAlong_iff, φ_UF q k φ hφx hφy, pow_mem_iff q k _ _ (pow_ne_zero 2 hq.out.ne_zero)]

theorem ord_UF_sub_pos_restrictAlong_iff (w : Place k (drinfeldFunctionField q k)) {a : k} (ha : a ^ q = a) :
    0 < (w.restrictAlong φ hφi).ord (UF q k - algebraMap k _ a) ↔ 0 < w.ord (UF q k - algebraMap k _ a) := by
  haveI := charP_k q k
  haveI := charP_F q k
  have haq : a ^ q ^ 2 = a := by rw [sq, pow_mul, ha, ha]
  rw [ord_restrictAlong_pos_iff, map_sub, φ_UF q k φ hφx hφy, AlgHom.commutes]
  conv_lhs => rw [← haq, map_pow, ← sub_pow_char_pow, ord_pow_nat]
  have hpos : (0 : ℤ) < (q ^ 2 : ℕ) := by exact_mod_cast pow_pos hq.out.pos 2
  rw [mul_pos_iff_of_pos_left hpos]

theorem restrictAlong_eq_smul_of_atInfinity (w : Place k (drinfeldFunctionField q k))
    (hw : xF q k ∉ w.toValuationSubring ∨ yF q k ∉ w.toValuationSubring) :
    w.restrictAlong φ hφi = ση q k η • w := by
  obtain ⟨hdir, -, huniq_a, huniq_inf⟩ := placesAtInfinity_census q k
  rcases (hdir w).mp hw with hinf | ⟨a, ha, hpos⟩
  ·
    have h1 : UF q k ∉ (w.restrictAlong φ hφi).toValuationSubring := (UF_not_mem_restrictAlong_iff q k φ hφi hφx hφy w).mpr hinf
    have h2 : UF q k ∉ (ση q k η • w).toValuationSubring := (UF_not_mem_smul_iff q k η w).mpr hinf
    exact huniq_inf.unique h1 h2
  ·
    have h1 := (ord_UF_sub_pos_restrictAlong_iff q k φ hφi hφx hφy w ha).mpr hpos
    have h2 := (ord_UF_sub_pos_smul_iff q k η w a).mpr hpos
    exact (huniq_a a ha).unique h1 h2

end InfTransport

end CNTAux

end DrinfeldCurve

end

open _root_.DrinfeldCurve _root_.P2MW.S_DrinfeldCurve_natCard_restrictAlong_eq_hFunctionFieldAction_one_smul_of_ne_neg_one.DrinfeldCurve in

theorem solution
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsAlgClosed k]
    [IsDomain (CoordRing q k)]
    (φ : drinfeldFunctionField q k →ₐ[k] drinfeldFunctionField q k) (hφi : φ.toRingHom.IsIntegral)
    (hφx : φ (algebraMap (CoordRing q k) (drinfeldFunctionField q k) (x q k)) =
      algebraMap (CoordRing q k) (drinfeldFunctionField q k) (x q k) ^ q ^ 2)
    (hφy : φ (algebraMap (CoordRing q k) (drinfeldFunctionField q k) (y q k)) =
      algebraMap (CoordRing q k) (drinfeldFunctionField q k) (y q k) ^ q ^ 2)
    (η : rootsOfUnity (q + 1) (GaloisField q 2)) (hη : ((η : (GaloisField q 2)ˣ) : GaloisField q 2) ≠ -1) :
    Nat.card {w : AlgebraicCurve.Place k (drinfeldFunctionField q k) //
        AlgebraicCurve.Place.restrictAlong φ hφi w =
          hFunctionFieldAction q k ⟨_, one_mem_hSubgroup_of_mem q η⟩ • w} = q + 1 := by
  obtain ⟨-, hcount, -, -⟩ := placesAtInfinity_census q k
  refine Eq.trans ?_ hcount
  apply Nat.card_congr
  refine Equiv.subtypeEquivRight (fun w => ⟨fun hrel => ?_,
    fun hw => CNTAux.restrictAlong_eq_smul_of_atInfinity q k φ hφi η hφx hφy w hw⟩)
  by_contra haff
  simp only [not_or, not_not] at haff
  obtain ⟨a, b, -, -, h1, h2, h3⟩ :=
    CNTAux.values_mem_affineFixed q k η φ hφi hφx hφy (CNTAux.isRational q k w) haff.1 haff.2 hrel
  obtain ⟨-, -, hempty⟩ := finite_and_ncard_setOf_twistedFrobenius_affineFixed q k η
  have hmem : ((a, b) : k × k) ∈ {p : k × k | p.1 * p.2 ^ q - p.1 ^ q * p.2 = 1 ∧
      algebraMap (GaloisField q 2) k ((η : (GaloisField q 2)ˣ) : GaloisField q 2) * p.1 ^ q ^ 2 = p.1 ∧
      algebraMap (GaloisField q 2) k ((η : (GaloisField q 2)ˣ) : GaloisField q 2) * p.2 ^ q ^ 2 = p.2} := ⟨h1, h2, h3⟩
  rw [hempty hη] at hmem
  exact hmem

end S_DrinfeldCurve_natCard_restrictAlong_eq_hFunctionFieldAction_one_smul_of_ne_neg_one
end P2MW
export P2MW.S_DrinfeldCurve_natCard_restrictAlong_eq_hFunctionFieldAction_one_smul_of_ne_neg_one (solution)
