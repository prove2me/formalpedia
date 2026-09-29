-- Prove2me | solution 1 for AutomorphicForm.torusShell_const_eq_of_forall_lintegral_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/29b8aa2d-fbfb-57d4-869d-7d15caf23d0c

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Theorems.Thm_AutomorphicForm_isFundamentalDomain_image_and_forall_setLIntegral_indicator_slab_bracket_eq_of_lintegral_eq
import Theorems.Thm_NumberField_AdelicHeight_exists_forall_measureReal_inter_ideleNorm_mem_Icc_eq_mul_log_and_setIntegral_weight_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_torusShell_const_eq_of_forall_lintegral_eq
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions in
open AutomorphicForm in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)

    (H : Subgroup (AdelicGL2 (𝓞 L) L)) (hHc : IsClosed (H : Set (AdelicGL2 (𝓞 L) L)))
    (hH : ∀ h : AdelicGL2 (𝓞 L) L, h ∈ H ↔
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0 ∧
       (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0 ∧
       AutomorphicForm.sigmaAdelicAct K L D σ h * h⁻¹ ∈ Subgroup.center (AdelicGL2 (𝓞 L) L)))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (Λ₀ : Subgroup (GL (Fin 2) L))
    (hΛ₀ : ∀ γ : GL (Fin 2) L, γ ∈ Λ₀ ↔ (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ Set.range (algebraMap K L))

    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ] (νK : Measure (AdeleRing (𝓞 K) K)ˣ)
    [νK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νK)
    (θ : (AdeleRing (𝓞 K) K)ˣ →* (AdeleRing (𝓞 L) L)ˣ) (hθ : Continuous θ) (hθi : Function.Injective θ)
    (hθn : ∀ a, NumberField.TateGlobal.ideleNorm L (θ a) = NumberField.TateGlobal.ideleNorm K a ^ Module.finrank K L)
    (hθc : ∀ k : Kˣ, θ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) k) =
      Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) (Units.map (algebraMap K L : K →* L) k))
    (cH : ℝ) (hcH : 0 < cH)
    (hμH : ∀ f : AdelicGL2 (𝓞 L) L → ENNReal, Measurable f →
      ∫⁻ h : H, f (h : AdelicGL2 (𝓞 L) L) ∂μH =
        ENNReal.ofReal cH * ∫⁻ z, ∫⁻ a, f (AutomorphicForm.centralScalar (𝓞 L) L z * diagOne (θ a)) ∂νK ∂νZL)
    (κ₀ : ℝ) (Ω : Set H)
    (hΩ : IsFundamentalDomain ((Λ₀.map (AutomorphicForm.globalPoints (𝓞 L) L)).subgroupOf H) Ω μH)
    (hκ₀ : ∀ (y : AdelicGL2 (𝓞 L) L) (R : ℝ),
      ∫⁻ h in Ω, ‖Set.indicator {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
            (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y) *
          ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y'}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y)
             - Set.indicator {y' : AdelicGL2 (𝓞 L) L |
                  Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y')}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y))‖ₑ ∂μH =
        ENNReal.ofReal (κ₀ * |2 * R - Real.log (NumberField.AdelicHeight.adelicHeight L y)
          - Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y))|)) :
    κ₀ = cH * (νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc 1 (Real.exp 1)})).toReal *
      (νK (ΩK ∩ {a | NumberField.TateGlobal.ideleNorm K a ∈ Set.Icc 1 (Real.exp 1)})).toReal *
      Real.log (β / α) / (2 * Module.finrank K L)  := by
  classical

  have hev := (AutomorphicForm.isFundamentalDomain_image_and_forall_setLIntegral_indicator_slab_bracket_eq_of_lintegral_eq
    K L α β hα hαβ νZL ΩL hΩL D σ hgen H hHc hH μH Λ₀ hΛ₀ νK ΩK hΩK θ hθ hθi hθn hθc cH hcH hμH).2 Ω hΩ
  set κf : ℝ := cH * (νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc 1 (Real.exp 1)})).toReal *
      (νK (ΩK ∩ {a | NumberField.TateGlobal.ideleNorm K a ∈ Set.Icc 1 (Real.exp 1)})).toReal *
      Real.log (β / α) / (2 * Module.finrank K L) with hκf

  obtain ⟨VL, hVL, hVL1, -⟩ :=
    NumberField.AdelicHeight.exists_forall_measureReal_inter_ideleNorm_mem_Icc_eq_mul_log_and_setIntegral_weight_comp_eq
      L L νZL ΩL hΩL (MonoidHom.id _) continuous_id 1 one_pos (fun y => by simp)
  obtain ⟨VK, hVK, hVK1, -⟩ :=
    NumberField.AdelicHeight.exists_forall_measureReal_inter_ideleNorm_mem_Icc_eq_mul_log_and_setIntegral_weight_comp_eq
      K L νK ΩK hΩK θ hθ (Module.finrank K L) Module.finrank_pos hθn
  have hVLeq : (νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc 1 (Real.exp 1)})).toReal = VL := by
    have := hVL1 1 (Real.exp 1) one_pos (by have := Real.add_one_le_exp (1:ℝ); linarith)
    rw [Real.log_exp, Real.log_one, sub_zero, mul_one] at this
    rw [← this, Measure.real]
  have hVKeq : (νK (ΩK ∩ {a | NumberField.TateGlobal.ideleNorm K a ∈ Set.Icc 1 (Real.exp 1)})).toReal = VK := by
    have := hVK1 1 (Real.exp 1) one_pos (by have := Real.add_one_le_exp (1:ℝ); linarith)
    rw [Real.log_exp, Real.log_one, sub_zero, mul_one] at this
    rw [← this, Measure.real]
  have hκfpos : 0 < κf := by
    rw [hκf, hVLeq, hVKeq]
    have h1 : 0 < Real.log (β / α) := Real.log_pos ((one_lt_div hα).mpr hαβ)
    have h2 : (0 : ℝ) < 2 * (Module.finrank K L : ℕ) := by
      have : (0 : ℝ) < (Module.finrank K L : ℕ) := by exact_mod_cast Module.finrank_pos
      linarith
    exact div_pos (mul_pos (mul_pos (mul_pos hcH hVL) hVK) h1) h2

  set R₁ : ℝ := (1 + Real.log (NumberField.AdelicHeight.adelicHeight L (1 : AdelicGL2 (𝓞 L) L)) +
    Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * 1))) / 2 with hR₁
  have hA : 2 * R₁ - Real.log (NumberField.AdelicHeight.adelicHeight L (1 : AdelicGL2 (𝓞 L) L)) -
      Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * 1)) = 1 := by
    rw [hR₁]; ring
  have h1 := (hev 1 R₁).1
  have h2 := hκ₀ 1 R₁
  rw [h2, hA] at h1
  simp only [abs_one, mul_one] at h1

  have hκf' : ENNReal.ofReal κ₀ = ENNReal.ofReal κf := by rw [hκf]; exact h1
  have hκ₀pos : 0 < κ₀ := by
    have : 0 < ENNReal.ofReal κ₀ := by rw [hκf']; exact ENNReal.ofReal_pos.mpr hκfpos
    exact ENNReal.ofReal_pos.mp this
  have := (ENNReal.ofReal_eq_ofReal_iff hκ₀pos.le hκfpos.le).mp hκf'
  rw [this, hκf]

end S_AutomorphicForm_torusShell_const_eq_of_forall_lintegral_eq
end P2MW
export P2MW.S_AutomorphicForm_torusShell_const_eq_of_forall_lintegral_eq (solution)
