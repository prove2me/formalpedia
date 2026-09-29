-- Prove2me | solution 1 for AutomorphicForm.withDensity_norm_inv_preimage_mul_eq_and_lt_top_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/df5d387f-ff02-5b04-a9d8-5bed83012769

import Theorems.Thm_NumberField_AdicCompletion_map_linearMap_eq_norm_det_inv_smul_of_isAddHaarMeasure
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_withDensity_norm_inv_preimage_mul_eq_and_lt_top_of_isCompact
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal Pointwise
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure] :
    (∀ (g : (L ⊗[K] v.adicCompletion K)ˣ) (X : Set (L ⊗[K] v.adicCompletion K)), MeasurableSet X →
      ν.withDensity (fun b => ENNReal.ofReal ‖Algebra.norm (v.adicCompletion K) b‖⁻¹)
          ((fun b : L ⊗[K] v.adicCompletion K => (g : L ⊗[K] v.adicCompletion K) * b) ⁻¹' X) =
        ν.withDensity (fun b => ENNReal.ofReal ‖Algebra.norm (v.adicCompletion K) b‖⁻¹) X) ∧
    (∀ Q : Set (L ⊗[K] v.adicCompletion K), IsCompact Q → (∀ q ∈ Q, IsUnit q) →
      ν.withDensity (fun b => ENNReal.ofReal ‖Algebra.norm (v.adicCompletion K) b‖⁻¹) Q ≠ ∞) := by
  classical
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI := AutomorphicForm.t2Space_tensor K L (v.adicCompletion K)

  have hNc : Continuous (Algebra.norm (v.adicCompletion K) :
      L ⊗[K] v.adicCompletion K → v.adicCompletion K) := by
    let bs := Module.finBasis (v.adicCompletion K) (L ⊗[K] v.adicCompletion K)
    have h : (Algebra.norm (v.adicCompletion K) : L ⊗[K] v.adicCompletion K → v.adicCompletion K) =
        fun s => (Algebra.leftMulMatrix bs s).det := funext (Algebra.norm_eq_matrix_det bs)
    rw [h]
    exact (IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix bs).toLinearMap).matrix_det
  have hmul : ∀ g : (L ⊗[K] v.adicCompletion K)ˣ,
      Continuous fun b : L ⊗[K] v.adicCompletion K => (g : L ⊗[K] v.adicCompletion K) * b :=
    fun g => continuous_const.mul continuous_id
  refine ⟨fun g X hX => ?_, fun Q hQc hQu => ?_⟩
  ·
    have hNg : Algebra.norm (v.adicCompletion K) (g : L ⊗[K] v.adicCompletion K) ≠ 0 :=
      ((Units.isUnit g).map (Algebra.norm (v.adicCompletion K))).ne_zero
    have hNg' : ‖Algebra.norm (v.adicCompletion K) (g : L ⊗[K] v.adicCompletion K)‖ ≠ 0 := norm_ne_zero_iff.2 hNg
    have hTdet : LinearMap.det (Algebra.lmul (v.adicCompletion K) (L ⊗[K] v.adicCompletion K)
        (g : L ⊗[K] v.adicCompletion K)) =
        Algebra.norm (v.adicCompletion K) (g : L ⊗[K] v.adicCompletion K) := (Algebra.norm_apply _ _).symm
    have hmap := NumberField.AdicCompletion.map_linearMap_eq_norm_det_inv_smul_of_isAddHaarMeasure K v
      (L ⊗[K] v.adicCompletion K) ν
      (Algebra.lmul (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) (g : L ⊗[K] v.adicCompletion K))
      (hTdet.symm ▸ hNg)
    rw [hTdet] at hmap

    let eh : L ⊗[K] v.adicCompletion K ≃ₜ L ⊗[K] v.adicCompletion K :=
      { toFun := fun b => (g : L ⊗[K] v.adicCompletion K) * b
        invFun := fun b => ((g⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) * b
        left_inv := fun b => Units.inv_mul_cancel_left g b
        right_inv := fun b => Units.mul_inv_cancel_left g b
        continuous_toFun := hmul g
        continuous_invFun := hmul g⁻¹ }
    let e := eh.toMeasurableEquiv
    have he : (⇑e : L ⊗[K] v.adicCompletion K → L ⊗[K] v.adicCompletion K) =
        fun b => (g : L ⊗[K] v.adicCompletion K) * b := rfl
    have hT : (⇑(Algebra.lmul (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) (g : L ⊗[K] v.adicCompletion K)) :
          L ⊗[K] v.adicCompletion K → L ⊗[K] v.adicCompletion K) =
        fun b => (g : L ⊗[K] v.adicCompletion K) * b := rfl
    rw [hT] at hmap

    have hind : ∀ b : L ⊗[K] v.adicCompletion K,
        ((fun b : L ⊗[K] v.adicCompletion K => (g : L ⊗[K] v.adicCompletion K) * b) ⁻¹' X).indicator
            (fun b => ENNReal.ofReal ‖Algebra.norm (v.adicCompletion K) b‖⁻¹) b =
          ENNReal.ofReal ‖Algebra.norm (v.adicCompletion K) (g : L ⊗[K] v.adicCompletion K)‖ *
            X.indicator (fun b => ENNReal.ofReal ‖Algebra.norm (v.adicCompletion K) b‖⁻¹)
              ((g : L ⊗[K] v.adicCompletion K) * b) := by
      intro b
      by_cases hb : (g : L ⊗[K] v.adicCompletion K) * b ∈ X
      · rw [Set.indicator_of_mem (show b ∈ _ ⁻¹' X from hb), Set.indicator_of_mem hb, map_mul, norm_mul,
          mul_inv, ENNReal.ofReal_mul (inv_nonneg.2 (norm_nonneg _)), ← mul_assoc,
          ← ENNReal.ofReal_mul (norm_nonneg _), mul_inv_cancel₀ hNg', ENNReal.ofReal_one, one_mul]
      · rw [Set.indicator_of_notMem (show b ∉ _ ⁻¹' X from hb), Set.indicator_of_notMem hb, mul_zero]
    rw [withDensity_apply _ (hX.preimage (hmul g).measurable), withDensity_apply _ hX,
      ← lintegral_indicator (hX.preimage (hmul g).measurable), ← lintegral_indicator hX]
    simp_rw [hind]
    have hcv : (∫⁻ a, X.indicator (fun b => ENNReal.ofReal ‖Algebra.norm (v.adicCompletion K) b‖⁻¹)
          ((g : L ⊗[K] v.adicCompletion K) * a) ∂ν) =
        ∫⁻ a, X.indicator (fun b => ENNReal.ofReal ‖Algebra.norm (v.adicCompletion K) b‖⁻¹) a
          ∂(Measure.map (fun b : L ⊗[K] v.adicCompletion K => (g : L ⊗[K] v.adicCompletion K) * b) ν) :=
      (lintegral_map_equiv _ e).symm
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hcv, hmap,
      lintegral_smul_measure, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul (norm_nonneg _), mul_inv_cancel₀ hNg',
      ENNReal.ofReal_one, one_mul]
  ·
    rcases Q.eq_empty_or_nonempty with hQe | hQne
    · rw [hQe, measure_empty]; exact ENNReal.zero_ne_top
    obtain ⟨q₀, hq₀, hmin⟩ := hQc.exists_isMinOn hQne (continuous_norm.comp hNc).continuousOn
    have hm : 0 < ‖Algebra.norm (v.adicCompletion K) q₀‖ :=
      norm_pos_iff.2 (((hQu q₀ hq₀).map (Algebra.norm (v.adicCompletion K))).ne_zero)
    have hQm : MeasurableSet Q := hQc.isClosed.measurableSet
    rw [withDensity_apply _ hQm]
    refine ne_top_of_le_ne_top ?_ (setLIntegral_mono' hQm fun q hq =>
      ENNReal.ofReal_le_ofReal (inv_anti₀ hm (hmin hq)))
    rw [setLIntegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hQc.measure_lt_top.ne

end S_AutomorphicForm_withDensity_norm_inv_preimage_mul_eq_and_lt_top_of_isCompact
end P2MW
export P2MW.S_AutomorphicForm_withDensity_norm_inv_preimage_mul_eq_and_lt_top_of_isCompact (solution)
