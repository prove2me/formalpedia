-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.rank_one_std
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:21:29.572327+00:00
-- url     : https://prove2.me/submissions/5041063e-7cef-43cc-adea-e4870e7b9a03

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_lintegral_pi_congr_coord
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_lin_subst
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_lintegral_insertFiber_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_exists_unit_orth
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_meas_gram_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_meas_gram

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormFactor
variable {Q : Type} [Fintype Q] [DecidableEq Q]
namespace Formalism.FourierDecayAlt.P.HermitianFormFactor
theorem _root_.solution (G₀ : (Q → Q → ℂ) → ℝ≥0∞) (hG : Measurable G₀) (h0 : ∀ T : Matrix Q Q ℂ, ¬ T.PosDef → G₀ T = 0)
    (j₀ : Q) :
    ∫⁻ X : Q → Q → ℂ, G₀ (gram X - Matrix.single j₀ j₀ (1 : ℂ)) = ∫⁻ X : Q → Q → ℂ, G₀ (gram X) := by
  refine lintegral_pi_congr_coord j₀ _ _ (meas_gram_sub G₀ hG _) (meas_gram G₀ hG) fun X => ?_
  obtain ⟨n, hn1, hnX⟩ := exists_unit_orth X j₀
  have hn0 : n ≠ 0 := by
    intro h; rw [h] at hn1; simp at hn1
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hn0
  have hi₀' : n i₀ ≠ 0 := hi₀
  have hLL : colL n 1 i₀ ∘ₗ colL n (-(n i₀)⁻¹) i₀ = LinearMap.id := by
    refine LinearMap.ext fun y => ?_
    funext l
    simp only [LinearMap.comp_apply, colL, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
      smul_eq_mul, Pi.single_eq_same, LinearMap.id_apply]
    field_simp
    ring
  obtain ⟨c, hc⟩ := lin_subst (volume : Measure (Q → ℂ)) _ _ hLL
  have hup : Continuous fun x : Q → ℂ => Function.update X j₀ x := continuous_const.update j₀ continuous_id
  refine (hc (fun x => G₀ (gram (Function.update X j₀ x) - Matrix.single j₀ j₀ (1 : ℂ)))
    ((meas_gram_sub G₀ hG _).comp hup.measurable)).trans (Eq.trans ?_ (hc (fun x => G₀ (gram (Function.update X j₀ x)))
    ((meas_gram G₀ hG).comp hup.measurable)).symm)
  congr 1
  have hLc : Continuous (colL n 1 i₀) := (colL n 1 i₀).continuous_of_finiteDimensional
  refine lintegral_pi_congr_coord i₀ _ _ (((meas_gram_sub G₀ hG _).comp hup.measurable).comp hLc.measurable)
    (((meas_gram G₀ hG).comp hup.measurable).comp hLc.measurable) fun x' => ?_
  have hL : ∀ z : ℂ, colL n 1 i₀ (Function.update x' i₀ z) = Function.update x' i₀ 0 + z • n := by
    intro z
    funext l
    simp only [colL, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
      Function.update_self, one_mul]
    by_cases hl : l = i₀
    · subst hl; simp; ring
    · simp [hl]
  simp_rw [hL]
  exact lintegral_insertFiber_le G₀ hG h0 X j₀ n hn1 hnX _
end Formalism.FourierDecayAlt.P.HermitianFormFactor
