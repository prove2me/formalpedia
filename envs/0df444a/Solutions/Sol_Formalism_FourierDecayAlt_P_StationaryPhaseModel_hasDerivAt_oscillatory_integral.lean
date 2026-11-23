-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.hasDerivAt_oscillatory_integral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:41:02.029481+00:00
-- url     : https://prove2.me/submissions/d8d54cf7-020c-4304-9abc-9fdaeb891d85

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_isAddHaar_muPi
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_norm_oscillatory_factor
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_continuous_oscillatory_factor
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_hasDerivAt_exp_linear_phase

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel
variable {d : ℕ} {β : ℂ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution (hβ : β ≠ 0) (φ₀ P : (Fin d → ℂ) → ℝ) (hφ₀ : Continuous φ₀) (hP : Continuous P) (τ : ℝ)
    (c : (Fin d → ℂ) → V) (hc : Continuous c) (hcs : HasCompactSupport c) (s : ℝ) :
    HasDerivAt (fun s : ℝ => ∫ x, osc (fun y => φ₀ y + s * P y) τ x • c x ∂(muPi β (Fin d)))
      (∫ x, osc (fun y => φ₀ y + s * P y) τ x • ((Complex.I * ((P x / τ : ℝ) : ℂ)) • c x) ∂(muPi β (Fin d))) s := by
  have := isAddHaar_muPi d β hβ
  have hcont : ∀ s : ℝ, Continuous (fun x => osc (fun y => φ₀ y + s * P y) τ x • c x) := fun s =>
    (continuous_oscillatory_factor (by fun_prop) τ).smul hc
  have hcont' : ∀ s : ℝ, Continuous
      (fun x => osc (fun y => φ₀ y + s * P y) τ x • ((Complex.I * ((P x / τ : ℝ) : ℂ)) • c x)) := fun s =>
    (continuous_oscillatory_factor (by fun_prop) τ).smul ((by fun_prop : Continuous fun x => (Complex.I * ((P x / τ : ℝ) : ℂ))).smul hc)
  have hb : Continuous (fun x => ‖P x / τ‖ * ‖c x‖) := by fun_prop
  have hbs : HasCompactSupport (fun x => ‖P x / τ‖ * ‖c x‖) := hcs.norm.mul_left
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := muPi β (Fin d)) (𝕜 := ℝ)
    (F := fun (s : ℝ) x => osc (fun y => φ₀ y + s * P y) τ x • c x)
    (F' := fun (s : ℝ) x => osc (fun y => φ₀ y + s * P y) τ x • ((Complex.I * ((P x / τ : ℝ) : ℂ)) • c x))
    (x₀ := s) (s := Set.univ) (bound := fun x => ‖P x / τ‖ * ‖c x‖) Filter.univ_mem
    (Filter.Eventually.of_forall fun s => (hcont s).aestronglyMeasurable)
    ((hcont s).integrable_of_hasCompactSupport hcs.smul_left)
    (hcont' s).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x s _ => by
      rw [norm_smul, norm_smul, norm_oscillatory_factor, one_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real])
    (hb.integrable_of_hasCompactSupport hbs)
    (Filter.Eventually.of_forall fun x s _ => by
      have h := (hasDerivAt_exp_linear_phase (φ₀ x) (P x) τ s).smul_const (c x)
      simp only [osc]
      convert h using 1
      rw [smul_smul, mul_comm])
  exact key.2
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
