-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.inner2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:41:23.974807+00:00
-- url     : https://prove2.me/submissions/f4b3ba4c-f9bf-4ad1-8684-7f53b450460d

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_frame_trans
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_invF_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_UH_unit
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_UH_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_lmF_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_rmF_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Bset_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Ff_act
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_meas_act_inv_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_ind_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_left


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
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {m P Q : Type} [Fintype m] [DecidableEq m] [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  {H : Matrix m m ℂ} {Ep : Matrix m P ℂ} {Em : Matrix m Q ℂ}
attribute [local instance] isAddHaarMeasure_matrix_volume
attribute [local instance] haar_prod2
namespace Formalism.FourierDecayAlt.P.HermitianFormFactor
theorem _root_.solution (F : Frame H Ep Em) (hH : IsUnit H.det) (μ : Measure (m → m → ℂ))
    (conc : ∀ᵐ g ∂μ, Matrix.of g ∈ UH H) (left : ∀ a ∈ UH H, μ.map (lmF a) = μ) (ρ : ℝ) (Y : Q → m → ℂ) :
    ∫⁻ g, Ff H Ep 1 (act (invF g) Y) * Ff H Ep ρ Y ∂μ = μ (invF ⁻¹' Bset Ep Em 1) * Ff H Ep ρ Y := by
  rw [lintegral_mul_const _ (meas_act_inv_left 1 Y)]
  by_cases hY : tb H Ep Y ∈ Kset P Q ρ
  · congr 1
    obtain ⟨gY, hgY, a, ha, hYe⟩ := frame_trans F (cm Y) hY.1
    have hψ : Measurable (fun g : m → m → ℂ => (Bset Ep Em 1).indicator (1 : (m → m → ℂ) → ℝ≥0∞)
        (rmF gY (invF g))) := (ind_meas 1).comp ((rmF_cont gY).measurable.comp invF_meas)
    calc ∫⁻ g, Ff H Ep 1 (act (invF g) Y) ∂μ
        = ∫⁻ g, (Bset Ep Em 1).indicator 1 (rmF gY (invF g)) ∂μ := by
          refine lintegral_congr_ae ?_
          filter_upwards [conc] with g hg
          exact Ff_act F hY hgY ha hYe (UH_inv hH hg)
      _ = ∫⁻ g, (Bset Ep Em 1).indicator 1 (rmF gY (invF g)) ∂(μ.map (lmF gY)) := by rw [left gY hgY]
      _ = ∫⁻ g, (Bset Ep Em 1).indicator 1 (invF g) ∂μ := by
          rw [lintegral_map hψ (lmF_cont gY).measurable]
          refine lintegral_congr fun g => ?_
          congr 1
          show (gY * Matrix.of g)⁻¹ * gY = (Matrix.of g)⁻¹
          rw [Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (UH_unit hH hgY), Matrix.mul_one]
      _ = μ (invF ⁻¹' Bset Ep Em 1) := by
          rw [← lintegral_indicator_one ((Bset_meas 1).preimage invF_meas)]
          rfl
  · have : Ff H Ep ρ Y = 0 := Set.indicator_of_notMem hY _
    rw [this, mul_zero, mul_zero]
end Formalism.FourierDecayAlt.P.HermitianFormFactor
