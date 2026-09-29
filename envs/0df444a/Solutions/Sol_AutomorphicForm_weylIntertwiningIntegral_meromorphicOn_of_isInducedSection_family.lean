-- Prove2me | solution 1 for AutomorphicForm.weylIntertwiningIntegral_meromorphicOn_of_isInducedSection_family
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/c8444737-ae89-5531-8bff-d67d5968d889

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_AutomorphicForm_exists_flat_isInducedSection_sum_eq_of_differentiable_family
import Theorems.Thm_AutomorphicForm_weylIntertwiningIntegral_meromorphicOn_of_flat_family
import Theorems.Thm_AutomorphicForm_weylIntertwiningIntegrand_integrable_of_re_gt_half
import Mathlib.Analysis.Complex.CauchyIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_weylIntertwiningIntegral_meromorphicOn_of_isInducedSection_family
p2m_attr_erase "instance" "instCountableOfNumberField_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions NumberField.AdelicCentre.locallyCompactSpace_adelicPGL2 NumberField.AdelicCentre.isTopologicalGroup_adelicPGL2 NumberField.AdelicCentre.t2Space_adelicPGL2 NumberField.AdelicCentre.isClosed_center instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LocalGL2.swapUnit_val LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq"
p2m_attr_erase "simp" "LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply"
set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.WindowedSiegel
open scoped NNReal

theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (_hμic : IsIdeleClassChar (𝓞 F) F μ) (_hνic : IsIdeleClassChar (𝓞 F) F ν)
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g))
      (g : AdelicGL2 (𝓞 F) F),
    letI := adeleBorel (𝓞 F) F
    ∃ M' : ℂ → ℂ, MeromorphicOn M' Set.univ
      ∧ ∀ s : ℂ, 1 / 2 < s.re → M' s
        = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) g := by
  intro α hα μ ν hμ hν hμic hνic φ hφ hφK hφf hφjc hφhol g

  obtain ⟨n, c, ψ, hc, hψ, hψK, hψf, hψjc, hψhol, hψflat, hsum⟩ :=
    exists_flat_isInducedSection_sum_eq_of_differentiable_family F hα μ ν φ hφ hφK hφf hφjc hφhol

  have hM := fun i : Fin n =>
    weylIntertwiningIntegral_meromorphicOn_of_flat_family F hα μ ν hμ hν hμic hνic (ψ i)
      (hψ i) (hψK i) (hψf i) (hψjc i) (hψflat i) g
  choose M hMmer hMeq using hM
  refine ⟨fun s => ∑ i, c i s * M i s, ?_, ?_⟩
  · intro z hz
    exact MeromorphicAt.fun_sum (s := Finset.univ)
      (fun i _ => ((hc i).analyticAt z).meromorphicAt.fun_mul (hMmer i z hz))
  · intro s hs
    have hcont : ∀ i, Continuous (ψ i s) := fun i =>
      Continuous.uncurry_left s (show Continuous (Function.uncurry (ψ i)) from hψjc i)
    have hint : ∀ i, Integrable (fun x : AdeleRing (𝓞 F) F =>
        ψ i s ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * g)) (adelicAddHaar (𝓞 F) F) :=
      fun i => weylIntertwiningIntegrand_integrable_of_re_gt_half F hα μ ν hμ hν s hs (ψ i s)
        (hψ i s) (hcont i) g
    have h1 : (∫ x, φ s ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * g) ∂(adelicAddHaar (𝓞 F) F))
        = ∫ x, ∑ i, c i s * ψ i s ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * g)
            ∂(adelicAddHaar (𝓞 F) F) := by
      simp_rw [hsum s]
    have h2 : (∫ x, ∑ i, c i s * ψ i s ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * g)
          ∂(adelicAddHaar (𝓞 F) F))
        = ∑ i, ∫ x, c i s * ψ i s ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * g)
            ∂(adelicAddHaar (𝓞 F) F) :=
      integral_finsetSum Finset.univ (fun i _ => (hint i).const_mul (c i s))
    have h3 : ∀ i, (∫ x, c i s * ψ i s ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * g)
          ∂(adelicAddHaar (𝓞 F) F))
        = c i s * M i s := by
      intro i
      rw [integral_const_mul, hMeq i s hs]
      rfl
    show ∑ i, c i s * M i s = ∫ x, φ s ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * g)
      ∂(adelicAddHaar (𝓞 F) F)
    rw [h1, h2]
    exact Finset.sum_congr rfl fun i _ => (h3 i).symm

#print axioms solution

end S_AutomorphicForm_weylIntertwiningIntegral_meromorphicOn_of_isInducedSection_family
end P2MW
export P2MW.S_AutomorphicForm_weylIntertwiningIntegral_meromorphicOn_of_isInducedSection_family (solution)
