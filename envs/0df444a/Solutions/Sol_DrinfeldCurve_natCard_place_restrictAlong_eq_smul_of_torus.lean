-- Prove2me | solution 1 for DrinfeldCurve.natCard_place_restrictAlong_eq_smul_of_torus
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/de5a7b9f-0bc2-5041-9df4-ac80fadb22d1

import Definitions.Def_DrinfeldCurve_FunctionField
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_CuspidalType_IsCuspidalOfType
import Mathlib
import Theorems.Thm_DrinfeldCurve_natCard_place_restrictAlong_eq_hFunctionFieldAction_smul
import Theorems.Thm_DrinfeldCurve_ncard_setOf_ellTwistedFrobenius_affineFixed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DrinfeldCurve_natCard_place_restrictAlong_eq_smul_of_torus
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

namespace DrinfeldCurve
p2m_export "DrinfeldCurve" "drinfeldFunctionField hFunctionFieldAction CoordRing mk x y ofZMod scalarOf coe_hChar_apply hSubgroup mem_hSubgroup_iff natCard_place_restrictAlong_eq_hFunctionFieldAction_smul ncard_setOf_ellTwistedFrobenius_affineFixed"
p2m_open "DrinfeldCurve"

namespace EllAux

open CuspidalType Polynomial

section F2

variable (q : ℕ) [hq : Fact q.Prime]

abbrev F2 : Type := GaloisField q 2

theorem pow_card_F2 (x : F2 q) : x ^ q ^ 2 = x := by
  haveI : Fintype (F2 q) := Fintype.ofFinite _
  have h : Fintype.card (F2 q) = q ^ 2 := by rw [Fintype.card_eq_nat_card, GaloisField.card q 2 two_ne_zero]
  rw [← h]; exact FiniteField.pow_card x

theorem pow_q_pow_q (x : F2 q) : (x ^ q) ^ q = x := by rw [← pow_mul, ← sq, pow_card_F2]

theorem algebraMap_zmod_pow (t : ZMod q) : (algebraMap (ZMod q) (F2 q) t) ^ q = algebraMap (ZMod q) (F2 q) t := by
  rw [← map_pow, ZMod.pow_card]

theorem mem_range_of_pow_eq {x : F2 q} (hx : x ^ q = x) : x ∈ Set.range (algebraMap (ZMod q) (F2 q)) := by
  classical
  have hq1 := hq.out.one_lt
  set P : (ZMod q)[X] := X ^ q - X with hP
  have hroots : P.roots = (Finset.univ : Finset (ZMod q)).val := by
    have h := FiniteField.roots_X_pow_card_sub_X (ZMod q)
    rwa [ZMod.card q] at h
  have hPdeg : P.natDegree = q := FiniteField.X_pow_card_sub_X_natDegree_eq (ZMod q) hq1
  have hmap : P.map (algebraMap (ZMod q) (F2 q)) = X ^ q - X := by
    rw [hP, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X]
  have hne : (X ^ q - X : (F2 q)[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero (F2 q) hq1
  have hle : P.roots.map (algebraMap (ZMod q) (F2 q)) ≤ (X ^ q - X : (F2 q)[X]).roots := by
    rw [← hmap]; exact Polynomial.map_roots_le (by rw [hmap]; exact hne)
  have hcard : (X ^ q - X : (F2 q)[X]).roots.card ≤ (P.roots.map (algebraMap (ZMod q) (F2 q))).card := by
    rw [Multiset.card_map, hroots]
    calc (X ^ q - X : (F2 q)[X]).roots.card ≤ (X ^ q - X : (F2 q)[X]).natDegree := Polynomial.card_roots' _
      _ = q := FiniteField.X_pow_card_sub_X_natDegree_eq (F2 q) hq1
      _ = _ := by simp [ZMod.card q]
  have heq := Multiset.eq_of_le_of_card_le hle hcard
  have hxr : x ∈ (X ^ q - X : (F2 q)[X]).roots := by
    rw [Polynomial.mem_roots hne, Polynomial.IsRoot, eval_sub, eval_pow, eval_X, hx, sub_self]
  rw [← heq, Multiset.mem_map] at hxr
  obtain ⟨t, -, ht⟩ := hxr
  exact ⟨t, ht⟩

variable (α : (F2 q)ˣ)

noncomputable abbrev gF : Matrix (Fin 2) (Fin 2) (F2 q) :=
  (((torus q α : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q))).map (algebraMap (ZMod q) (F2 q))

noncomputable def e (i : Fin 2) : F2 q := quadBasis q i
theorem e_def (i : Fin 2) : e q i = quadBasis q i := rfl
noncomputable abbrev f (i : Fin 2) : F2 q := e q i ^ q

theorem e_vecMul (j : Fin 2) : ∑ i, e q i * gF q α i j = (α : F2 q) * e q j := by
  have hT : ((torus q α : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) =
      LinearMap.toMatrix (quadBasis q) (quadBasis q) (Algebra.lmul (ZMod q) (F2 q) (α : F2 q)) := rfl
  simp only [gF, e_def, Matrix.map_apply, hT, LinearMap.toMatrix_apply]
  have key := (quadBasis q).sum_repr ((α : F2 q) * quadBasis q j)
  conv_rhs => rw [← key]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, mul_comm]
  rfl

theorem e_vecMul' (j : Fin 2) : e q 0 * gF q α 0 j + e q 1 * gF q α 1 j = (α : F2 q) * e q j := by
  rw [← e_vecMul q α j, Fin.sum_univ_two]

theorem gF_pow (i j : Fin 2) : gF q α i j ^ q = gF q α i j := by
  simp only [gF, Matrix.map_apply]; exact algebraMap_zmod_pow q _

theorem f_vecMul' (j : Fin 2) : f q 0 * gF q α 0 j + f q 1 * gF q α 1 j = (α : F2 q) ^ q * f q j := by
  have h := congrArg (fun z : F2 q => z ^ q) (e_vecMul' q α j)
  simp only [add_pow_char, mul_pow, gF_pow] at h
  exact h

theorem f_pow (i : Fin 2) : f q i ^ q = e q i := pow_q_pow_q q _

theorem e_ne_zero (i : Fin 2) : e q i ≠ 0 := by rw [e_def]; exact (quadBasis q).ne_zero i

noncomputable def δ : F2 q := e q 0 * f q 1 - e q 1 * f q 0

theorem δ_pow : δ q ^ q = -δ q := by
  rw [δ, sub_pow_char, mul_pow, mul_pow, f_pow, f_pow]
  ring

theorem δ_ne_zero : δ q ≠ 0 := by
  intro h
  have h0 := e_ne_zero q 0

  have ht : (e q 1 / e q 0) ^ q = e q 1 / e q 0 := by
    rw [δ, sub_eq_zero] at h
    rw [div_pow, div_eq_div_iff (pow_ne_zero _ h0) h0]
    linear_combination h
  obtain ⟨t, ht'⟩ := mem_range_of_pow_eq q ht

  have hlin := (quadBasis q).linearIndependent
  rw [Fintype.linearIndependent_iff] at hlin
  have hrel : t • quadBasis q 0 + (-1 : ZMod q) • quadBasis q 1 = 0 := by
    rw [Algebra.smul_def, Algebra.smul_def, ht', map_neg, map_one, ← e_def, ← e_def, div_mul_cancel₀ _ h0]; ring
  have := hlin ![t, -1] (by simpa [Fin.sum_univ_two] using hrel) 1
  simp at this

theorem eq_zero_of_combination {L : Type*} [Field L] [Algebra (F2 q) L] {a b : L}
    (h0 : a * algebraMap (F2 q) L (e q 0) + b * algebraMap (F2 q) L (f q 0) = 0)
    (h1 : a * algebraMap (F2 q) L (e q 1) + b * algebraMap (F2 q) L (f q 1) = 0) : a = 0 ∧ b = 0 := by
  have hδ : algebraMap (F2 q) L (δ q) ≠ 0 := (_root_.map_ne_zero _).mpr (δ_ne_zero q)
  rw [δ, map_sub, map_mul, map_mul] at hδ
  constructor
  · have : a * (algebraMap (F2 q) L (e q 0) * algebraMap (F2 q) L (f q 1) -
        algebraMap (F2 q) L (e q 1) * algebraMap (F2 q) L (f q 0)) = 0 := by
      linear_combination (algebraMap (F2 q) L (f q 1)) * h0 - (algebraMap (F2 q) L (f q 0)) * h1
    exact (mul_eq_zero.mp this).resolve_right hδ
  · have : b * (algebraMap (F2 q) L (e q 0) * algebraMap (F2 q) L (f q 1) -
        algebraMap (F2 q) L (e q 1) * algebraMap (F2 q) L (f q 0)) = 0 := by
      linear_combination (algebraMap (F2 q) L (e q 0)) * h1 - (algebraMap (F2 q) L (e q 1)) * h0
    exact (mul_eq_zero.mp this).resolve_right hδ

variable {α}
variable (hα : (α : F2 q) ∉ Set.range (algebraMap (ZMod q) (F2 q)))

include hα in
theorem α_pow_ne : (α : F2 q) ^ q ≠ (α : F2 q) := fun h => hα (mem_range_of_pow_eq q h)

include hα in

theorem no_rational_eigenrow (r : Fin 2 → ZMod q) (μ : ZMod q)
    (h : ∀ j, r 0 * ((torus q α : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 j +
      r 1 * ((torus q α : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 j = μ * r j) : r 0 = 0 ∧ r 1 = 0 := by

  set φ := algebraMap (ZMod q) (F2 q) with hφ
  set R : Fin 2 → F2 q := fun i => φ (r i) with hR
  have hRq : ∀ i, R i ^ q = R i := fun i => algebraMap_zmod_pow q _
  have hg : ∀ i j, φ (((torus q α : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) i j) = gF q α i j := fun i j => rfl
  have h' : ∀ j, R 0 * gF q α 0 j + R 1 * gF q α 1 j = φ μ * R j := by
    intro j; have := congrArg φ (h j); simpa [hR, hg, map_add, map_mul] using this

  have hδ := δ_ne_zero q
  set s₁ : F2 q := (R 0 * f q 1 - R 1 * f q 0) / δ q with hs₁
  set s₂ : F2 q := (R 1 * e q 0 - R 0 * e q 1) / δ q with hs₂
  have hdec0 : R 0 = s₁ * e q 0 + s₂ * f q 0 := by
    rw [hs₁, hs₂, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hδ, δ]
    ring
  have hdec1 : R 1 = s₁ * e q 1 + s₂ * f q 1 := by
    rw [hs₁, hs₂, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hδ, δ]
    ring
  have hdec : ∀ j, R j = s₁ * e q j + s₂ * f q j := fun j => by
    fin_cases j
    · exact hdec0
    · exact hdec1

  have hE0 := e_vecMul' q α
  have hF0 := f_vecMul' q α
  have hcomb : ∀ j, (s₁ * ((α : F2 q) - φ μ)) * e q j + (s₂ * ((α : F2 q) ^ q - φ μ)) * f q j = 0 := by
    intro j
    have hj := h' j
    rw [hdec 0, hdec 1, hdec j] at hj
    linear_combination hj - s₁ * hE0 j - s₂ * hF0 j
  obtain ⟨h1, h2⟩ := eq_zero_of_combination q (L := F2 q) (a := s₁ * ((α : F2 q) - φ μ))
    (b := s₂ * ((α : F2 q) ^ q - φ μ)) (by simpa using hcomb 0) (by simpa using hcomb 1)
  have hαμ : (α : F2 q) - φ μ ≠ 0 := sub_ne_zero.mpr fun h => hα ⟨μ, h.symm⟩
  have hαqμ : (α : F2 q) ^ q - φ μ ≠ 0 := sub_ne_zero.mpr fun h => hα ⟨μ, by
    rw [← pow_q_pow_q q (α : F2 q), h]; exact (algebraMap_zmod_pow q μ).symm⟩
  have hs1 : s₁ = 0 := (mul_eq_zero.mp h1).resolve_right hαμ
  have hs2 : s₂ = 0 := (mul_eq_zero.mp h2).resolve_right hαqμ
  have hR0 : ∀ j, R j = 0 := fun j => by rw [hdec j, hs1, hs2]; ring
  have hinj := (algebraMap (ZMod q) (F2 q)).injective
  exact ⟨hinj (by simpa [hR] using hR0 0), hinj (by simpa [hR] using hR0 1)⟩

end F2

section Kside

variable (q : ℕ) [hq : Fact q.Prime] (K : Type*) [Field K] [Algebra (GaloisField q 2) K]

abbrev ι : F2 q →+* K := algebraMap (F2 q) K

theorem charP_K : CharP K q := charP_of_injective_algebraMap' (F2 q) q

noncomputable abbrev E (i : Fin 2) : K := ι q K (e q i)
noncomputable abbrev F (i : Fin 2) : K := ι q K (f q i)

theorem E_pow (i : Fin 2) : E q K i ^ q = F q K i := by rw [E, F, ← map_pow]
theorem F_pow (i : Fin 2) : F q K i ^ q = E q K i := by rw [E, F, ← map_pow, f_pow]
theorem E_pow2 (i : Fin 2) : E q K i ^ q ^ 2 = E q K i := by rw [sq, pow_mul, E_pow, F_pow]
theorem F_pow2 (i : Fin 2) : F q K i ^ q ^ 2 = F q K i := by rw [sq, pow_mul, F_pow, E_pow]

theorem Δ_ne_zero : E q K 0 * F q K 1 - E q K 1 * F q K 0 ≠ 0 := by
  have h : ι q K (δ q) ≠ 0 := (_root_.map_ne_zero _).mpr (δ_ne_zero q)
  rwa [δ, map_sub, map_mul, map_mul] at h

noncomputable def Φ (u : K × K) : K × K := (u.1 * E q K 0 + u.2 * F q K 0, u.1 * E q K 1 + u.2 * F q K 1)

theorem Φ_injective : Function.Injective (Φ q K) := by
  intro u u' h
  simp only [Φ, Prod.mk.injEq] at h
  obtain ⟨h0, h1⟩ := h
  have := eq_zero_of_combination q (L := K) (a := u.1 - u'.1) (b := u.2 - u'.2)
    (by rw [sub_mul, sub_mul]; linear_combination h0) (by rw [sub_mul, sub_mul]; linear_combination h1)
  exact Prod.ext (sub_eq_zero.mp this.1) (sub_eq_zero.mp this.2)

theorem Φ_surjective : Function.Surjective (Φ q K) := by
  intro v
  have hΔ := Δ_ne_zero q K
  set A : K := (v.1 * F q K 1 - v.2 * F q K 0) / (E q K 0 * F q K 1 - E q K 1 * F q K 0) with hA
  set B : K := (v.2 * E q K 0 - v.1 * E q K 1) / (E q K 0 * F q K 1 - E q K 1 * F q K 0) with hB
  refine ⟨(A, B), Prod.ext ?_ ?_⟩
  · show A * E q K 0 + B * F q K 0 = v.1
    rw [hA, hB, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hΔ]; ring
  · show A * E q K 1 + B * F q K 1 = v.2
    rw [hA, hB, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hΔ]; ring

variable (α : (F2 q)ˣ)

theorem E_vecMul (j : Fin 2) : E q K 0 * ι q K (gF q α 0 j) + E q K 1 * ι q K (gF q α 1 j) = ι q K α * E q K j := by
  have h := congrArg (ι q K) (e_vecMul' q α j)
  simpa [map_add, map_mul] using h

theorem F_vecMul (j : Fin 2) : F q K 0 * ι q K (gF q α 0 j) + F q K 1 * ι q K (gF q α 1 j) = ι q K ((α : F2 q) ^ q) * F q K j := by
  have h := congrArg (ι q K) (f_vecMul' q α j)
  simpa [map_add, map_mul] using h

theorem form_Φ (u : K × K) :
    (Φ q K u).1 * (Φ q K u).2 ^ q - (Φ q K u).1 ^ q * (Φ q K u).2 =
      (u.1 ^ (q + 1) - u.2 ^ (q + 1)) * (E q K 0 * F q K 1 - E q K 1 * F q K 0) := by
  haveI := charP_K q K
  simp only [Φ]
  rw [add_pow_char, add_pow_char, mul_pow, mul_pow, mul_pow, mul_pow, E_pow, E_pow, F_pow, F_pow, pow_succ, pow_succ]
  ring

theorem twist_Φ_iff (ζ : F2 q) (u : K × K) :
    (ι q K ζ * (ι q K (gF q α 0 0) * (Φ q K u).1 ^ q ^ 2 + ι q K (gF q α 1 0) * (Φ q K u).2 ^ q ^ 2) = (Φ q K u).1 ∧
      ι q K ζ * (ι q K (gF q α 0 1) * (Φ q K u).1 ^ q ^ 2 + ι q K (gF q α 1 1) * (Φ q K u).2 ^ q ^ 2) = (Φ q K u).2) ↔
    (ι q K (ζ * α) * u.1 ^ q ^ 2 = u.1 ∧ ι q K (ζ * (α : F2 q) ^ q) * u.2 ^ q ^ 2 = u.2) := by
  haveI := charP_K q K

  have hp1 : (Φ q K u).1 ^ q ^ 2 = u.1 ^ q ^ 2 * E q K 0 + u.2 ^ q ^ 2 * F q K 0 := by
    simp only [Φ]; rw [add_pow_char_pow, mul_pow, mul_pow, E_pow2, F_pow2]
  have hp2 : (Φ q K u).2 ^ q ^ 2 = u.1 ^ q ^ 2 * E q K 1 + u.2 ^ q ^ 2 * F q K 1 := by
    simp only [Φ]; rw [add_pow_char_pow, mul_pow, mul_pow, E_pow2, F_pow2]
  have hE := E_vecMul q K α
  have hF := F_vecMul q K α

  set X : K := ι q K (ζ * α) * u.1 ^ q ^ 2 - u.1 with hX
  set Y : K := ι q K (ζ * (α : F2 q) ^ q) * u.2 ^ q ^ 2 - u.2 with hY
  have hc1 : ι q K ζ * (ι q K (gF q α 0 0) * (Φ q K u).1 ^ q ^ 2 + ι q K (gF q α 1 0) * (Φ q K u).2 ^ q ^ 2) - (Φ q K u).1 =
      X * E q K 0 + Y * F q K 0 := by
    rw [hp1, hp2, hX, hY, map_mul, map_mul]
    simp only [Φ]
    linear_combination (ι q K ζ * u.1 ^ q ^ 2) * hE 0 + (ι q K ζ * u.2 ^ q ^ 2) * hF 0
  have hc2 : ι q K ζ * (ι q K (gF q α 0 1) * (Φ q K u).1 ^ q ^ 2 + ι q K (gF q α 1 1) * (Φ q K u).2 ^ q ^ 2) - (Φ q K u).2 =
      X * E q K 1 + Y * F q K 1 := by
    rw [hp1, hp2, hX, hY, map_mul, map_mul]
    simp only [Φ]
    linear_combination (ι q K ζ * u.1 ^ q ^ 2) * hE 1 + (ι q K ζ * u.2 ^ q ^ 2) * hF 1
  constructor
  · rintro ⟨h1, h2⟩
    have e1 : X * E q K 0 + Y * F q K 0 = 0 := by rw [← hc1, h1, sub_self]
    have e2 : X * E q K 1 + Y * F q K 1 = 0 := by rw [← hc2, h2, sub_self]
    obtain ⟨hX0, hY0⟩ := eq_zero_of_combination q (L := K) e1 e2
    exact ⟨sub_eq_zero.mp hX0, sub_eq_zero.mp hY0⟩
  · rintro ⟨h1, h2⟩
    have hX0 : X = 0 := sub_eq_zero.mpr h1
    have hY0 : Y = 0 := sub_eq_zero.mpr h2
    constructor
    · rw [← sub_eq_zero, hc1, hX0, hY0]; ring
    · rw [← sub_eq_zero, hc2, hX0, hY0]; ring

end Kside

section Assembly

variable (q : ℕ) [hq : Fact q.Prime]

theorem det_gF (α : (F2 q)ˣ) : (gF q α).det = (α : F2 q) * (α : F2 q) ^ q := by
  have hδ := δ_ne_zero q
  have hE := e_vecMul' q α
  have hF := f_vecMul' q α
  have key : δ q * (gF q α).det = δ q * ((α : F2 q) * (α : F2 q) ^ q) := by
    rw [Matrix.det_fin_two, δ]
    linear_combination (f q 0 * gF q α 0 1 + f q 1 * gF q α 1 1) * hE 0 - (f q 0 * gF q α 0 0 + f q 1 * gF q α 1 0) * hE 1
      + ((α : F2 q) * e q 0) * hF 1 - ((α : F2 q) * e q 1) * hF 0
  exact mul_left_cancel₀ hδ key

theorem neg_inv_eq_iff (ζ β : (F2 q)ˣ) : -ζ⁻¹ = β ↔ (ζ : F2 q) * (β : F2 q) = -1 := by
  rw [Units.ext_iff, Units.val_neg, Units.val_inv_eq_inv_val]
  have hζ : (ζ : F2 q) ≠ 0 := Units.ne_zero ζ
  constructor
  · intro h; rw [← h, mul_neg, mul_inv_cancel₀ hζ]
  · intro h
    have : (β : F2 q) = (ζ : F2 q)⁻¹ * ((ζ : F2 q) * β) := by rw [← mul_assoc, inv_mul_cancel₀ hζ, one_mul]
    rw [this, h, mul_neg, mul_one]

theorem inv_eq_neg_one_iff (z : F2 q) : z⁻¹ = -1 ↔ z = -1 := by
  rw [inv_eq_iff_eq_inv, inv_neg, inv_one]

variable (k : Type) [Field k] [Algebra (GaloisField q 2) k]

theorem ofZMod_torus (α : (F2 q)ˣ) (i j : Fin 2) :
    ofZMod q k (((torus q α : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) i j) = ι q k (gF q α i j) := rfl

theorem scalarOf_eq (ζ : (F2 q)ˣ) : scalarOf q k ζ = ι q k (ζ : F2 q) := rfl

end Assembly

end EllAux

end DrinfeldCurve

open _root_.DrinfeldCurve _root_.P2MW.S_DrinfeldCurve_natCard_place_restrictAlong_eq_smul_of_torus.DrinfeldCurve DrinfeldCurve.EllAux CuspidalType in
theorem solution
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsAlgClosed k]
    [IsDomain (CoordRing q k)] [AlgebraicCurve.IsCurveOver k (drinfeldFunctionField q k)]
    (φ : drinfeldFunctionField q k →ₐ[k] drinfeldFunctionField q k) (hφi : φ.toRingHom.IsIntegral)
    (hφx : φ (algebraMap (CoordRing q k) (drinfeldFunctionField q k) (x q k)) =
      algebraMap (CoordRing q k) (drinfeldFunctionField q k) (x q k) ^ q ^ 2)
    (hφy : φ (algebraMap (CoordRing q k) (drinfeldFunctionField q k) (y q k)) =
      algebraMap (CoordRing q k) (drinfeldFunctionField q k) (y q k) ^ q ^ 2)
    (α : (GaloisField q 2)ˣ) (hα : (α : GaloisField q 2) ∉ Set.range (algebraMap (ZMod q) (GaloisField q 2)))
    (ζ : (GaloisField q 2)ˣ)
    (hmem : ((torus q α, ζ) : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ) ∈ hSubgroup q) :
    ((-ζ⁻¹ = α ∨ -ζ⁻¹ = α ^ q) →
      Nat.card {w : AlgebraicCurve.Place k (drinfeldFunctionField q k) //
          AlgebraicCurve.Place.restrictAlong φ hφi w = hFunctionFieldAction q k ⟨_, hmem⟩ • w} = q + 1) ∧
    (¬ (-ζ⁻¹ = α ∨ -ζ⁻¹ = α ^ q) →
      Nat.card {w : AlgebraicCurve.Place k (drinfeldFunctionField q k) //
          AlgebraicCurve.Place.restrictAlong φ hφi w = hFunctionFieldAction q k ⟨_, hmem⟩ • w} = (q + 1) ^ 2) := by
  have hq : Fact q.Prime := inferInstance
  haveI := charP_K q k

  have hgen := natCard_place_restrictAlong_eq_hFunctionFieldAction_smul q k φ hφi hφx hφy ⟨_, hmem⟩
  simp only at hgen

  have hinf : Nat.card {t : ZMod q // t * ((torus q α : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0 +
      ((torus q α : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 =
      t * (t * ((torus q α : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 1 +
        ((torus q α : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 1)} = 0 := by
    rw [Nat.card_eq_zero]
    left
    refine ⟨fun ⟨t, ht⟩ => ?_⟩
    have h := no_rational_eigenrow q hα ![t, 1]
      (t * ((torus q α : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 1 + ((torus q α : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 1)
      (Fin.forall_fin_two.mpr ⟨by
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, one_mul]
          rw [ht]; ring,
        by simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, one_mul, mul_one]⟩)
    simpa using h.2
  have h01 : ((torus q α : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 1 ≠ 0 := by
    intro h0
    have h := no_rational_eigenrow q hα ![1, 0] (((torus q α : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0)
      (Fin.forall_fin_two.mpr ⟨by
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, one_mul, zero_mul, add_zero, mul_one],
        by simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, one_mul, zero_mul, add_zero,
          mul_zero, h0]⟩)
    simpa using h.1
  rw [hinf, if_neg h01, add_zero, add_zero] at hgen

  have hH : ((ζ : F2 q) * α) ^ (q + 1) = 1 := by
    have h := (mem_hSubgroup_iff q _).mp hmem
    have h' := congrArg (fun z : (F2 q)ˣ => (z : F2 q)) h
    simp only [coe_hChar_apply, Units.val_one] at h'
    rw [RingHom.map_det, RingHom.mapMatrix_apply, show (((torus q α : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q))).map
      (algebraMap (ZMod q) (F2 q)) = gF q α from rfl, det_gF] at h'
    rw [mul_pow, pow_succ (α : F2 q)]
    linear_combination h'
  have hαq : ((α : F2 q) ^ (q + 1)) ^ q = (α : F2 q) ^ (q + 1) := by
    rw [← pow_mul, show (q + 1) * q = q ^ 2 + q by ring, pow_add, pow_card_F2, pow_succ, mul_comm]
  have hH' : ((ζ : F2 q) * (α : F2 q) ^ q) ^ (q + 1) = 1 := by
    rw [mul_pow, ← pow_mul, mul_comm q (q + 1), pow_mul, hαq, ← mul_pow]; exact hH
  have hζ0 : (ζ : F2 q) ≠ 0 := Units.ne_zero ζ
  have hα0 : (α : F2 q) ≠ 0 := Units.ne_zero α
  have hζα : (ζ : F2 q) * α ≠ 0 := mul_ne_zero hζ0 hα0
  have hζαq : (ζ : F2 q) * (α : F2 q) ^ q ≠ 0 := mul_ne_zero hζ0 (pow_ne_zero _ hα0)

  obtain ⟨l₁, hl₁⟩ : ∃ l : F2 q, l = ((ζ : F2 q) * α)⁻¹ := ⟨_, rfl⟩
  obtain ⟨l₂, hl₂⟩ : ∃ l : F2 q, l = ((ζ : F2 q) * (α : F2 q) ^ q)⁻¹ := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d' : F2 q, d' = (δ q)⁻¹ := ⟨_, rfl⟩
  have h12 : l₁ ≠ l₂ := by
    rw [hl₁, hl₂, Ne, inv_inj, mul_right_inj' hζ0]
    exact (α_pow_ne q hα).symm
  have hl1 : l₁ ^ (q + 1) = 1 := by rw [hl₁, inv_pow, hH, inv_one]
  have hl2 : l₂ ^ (q + 1) = 1 := by rw [hl₂, inv_pow, hH', inv_one]
  have hdq : d ^ q = -d := by rw [hd, inv_pow, δ_pow, inv_neg]
  have hd0 : d ≠ 0 := by rw [hd]; exact inv_ne_zero (δ_ne_zero q)

  obtain ⟨hE1, hE2⟩ := ncard_setOf_ellTwistedFrobenius_affineFixed q k l₁ l₂ d h12 hl1 hl2 hdq hd0
  obtain ⟨T, hT⟩ : ∃ T : Set (k × k), T = {u : k × k | u.1 ^ q ^ 2 = algebraMap (GaloisField q 2) k l₁ * u.1 ∧
      u.2 ^ q ^ 2 = algebraMap (GaloisField q 2) k l₂ * u.2 ∧
      u.1 ^ (q + 1) - u.2 ^ (q + 1) = algebraMap (GaloisField q 2) k d} := ⟨_, rfl⟩
  rw [← hT] at hE1 hE2

  have hΔ := Δ_ne_zero q k
  have hΔ' : ι q k (δ q) = E q k 0 * F q k 1 - E q k 1 * F q k 0 := by rw [δ, map_sub, map_mul, map_mul]
  have hιδ : ι q k (δ q) ≠ 0 := by rw [hΔ']; exact hΔ
  have hια : ι q k ((ζ : F2 q) * α) ≠ 0 := (_root_.map_ne_zero _).mpr hζα
  have hιαq : ι q k ((ζ : F2 q) * (α : F2 q) ^ q) ≠ 0 := (_root_.map_ne_zero _).mpr hζαq
  have key : ∀ u : k × k, (Φ q k u ∈ {ab : k × k | ab.1 * ab.2 ^ q - ab.1 ^ q * ab.2 = 1 ∧
      scalarOf q k ζ * (ofZMod q k (((torus q α : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0) * ab.1 ^ q ^ 2 +
        ofZMod q k (((torus q α : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0) * ab.2 ^ q ^ 2) = ab.1 ∧
      scalarOf q k ζ * (ofZMod q k (((torus q α : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 1) * ab.1 ^ q ^ 2 +
        ofZMod q k (((torus q α : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 1) * ab.2 ^ q ^ 2) = ab.2}) ↔ u ∈ T := by
    intro u
    simp only [Set.mem_setOf_eq, ofZMod_torus, scalarOf_eq]
    rw [form_Φ, twist_Φ_iff, hT, Set.mem_setOf_eq, hl₁, hl₂, hd, map_inv₀, map_inv₀, map_inv₀,
      eq_inv_mul_iff_mul_eq₀ hια, eq_inv_mul_iff_mul_eq₀ hιαq, ← one_mul ((ι q k (δ q))⁻¹),
      eq_mul_inv_iff_mul_eq₀ hιδ, hΔ']
    exact ⟨fun ⟨hD, h1, h2⟩ => ⟨h1, h2, hD⟩, fun ⟨h1, h2, hD⟩ => ⟨hD, h1, h2⟩⟩
  have hSeq : {ab : k × k | ab.1 * ab.2 ^ q - ab.1 ^ q * ab.2 = 1 ∧
      scalarOf q k ζ * (ofZMod q k (((torus q α : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0) * ab.1 ^ q ^ 2 +
        ofZMod q k (((torus q α : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0) * ab.2 ^ q ^ 2) = ab.1 ∧
      scalarOf q k ζ * (ofZMod q k (((torus q α : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 1) * ab.1 ^ q ^ 2 +
        ofZMod q k (((torus q α : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 1) * ab.2 ^ q ^ 2) = ab.2} = Φ q k '' T := by
    ext v
    constructor
    · intro hv
      obtain ⟨u, rfl⟩ := Φ_surjective q k v
      exact ⟨u, (key u).mp hv, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact (key u).mpr hu
  rw [hSeq, Set.ncard_image_of_injective _ (Φ_injective q k)] at hgen

  have hiff : (l₁ = -1 ∨ l₂ = -1) ↔ (-ζ⁻¹ = α ∨ -ζ⁻¹ = α ^ q) := by
    rw [hl₁, hl₂, inv_eq_neg_one_iff, inv_eq_neg_one_iff, neg_inv_eq_iff, neg_inv_eq_iff, Units.val_pow_eq_pow_val]
  constructor
  · intro hs; rw [hgen]; exact hE1 (hiff.mpr hs)
  · intro hs; rw [hgen]; exact hE2 (fun h => hs (hiff.mp h))

end S_DrinfeldCurve_natCard_place_restrictAlong_eq_smul_of_torus
end P2MW
export P2MW.S_DrinfeldCurve_natCard_place_restrictAlong_eq_smul_of_torus (solution)
