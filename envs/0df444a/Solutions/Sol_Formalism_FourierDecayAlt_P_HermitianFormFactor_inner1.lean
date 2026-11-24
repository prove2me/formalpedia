-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.inner1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:23:23.408795+00:00
-- url     : https://prove2.me/submissions/7576e219-6ac5-4a39-8f5c-c1066e238e89

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_frame_trans
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_rmF_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Bset_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Ff_act
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_meas_act_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_ind_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_right


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
theorem _root_.solution (F : Frame H Ep Em) (μ : Measure (m → m → ℂ))
    (conc : ∀ᵐ g ∂μ, Matrix.of g ∈ UH H) (right : ∀ a ∈ UH H, μ.map (rmF a) = μ) (ρ : ℝ) (Y : Q → m → ℂ) :
    ∫⁻ g, Ff H Ep 1 Y * Ff H Ep ρ (act g Y) ∂μ = Ff H Ep 1 Y * μ (Bset Ep Em ρ) := by
  rw [lintegral_const_mul _ (meas_act_left ρ Y)]
  by_cases hY : tb H Ep Y ∈ Kset P Q 1
  · congr 1
    obtain ⟨gY, hgY, a, ha, hYe⟩ := frame_trans F (cm Y) hY.1
    calc ∫⁻ g, Ff H Ep ρ (act g Y) ∂μ
        = ∫⁻ g, (Bset Ep Em ρ).indicator 1 (rmF gY g) ∂μ := by
          refine lintegral_congr_ae ?_
          filter_upwards [conc] with g hg
          exact Ff_act F hY hgY ha hYe hg
      _ = ∫⁻ g, (Bset Ep Em ρ).indicator 1 g ∂(μ.map (rmF gY)) :=
          (lintegral_map (ind_meas ρ) (rmF_cont gY).measurable).symm
      _ = μ (Bset Ep Em ρ) := by rw [right gY hgY, lintegral_indicator_one (Bset_meas ρ)]
  · have : Ff H Ep 1 Y = 0 := Set.indicator_of_notMem hY _
    rw [this, zero_mul, zero_mul]
end Formalism.FourierDecayAlt.P.HermitianFormFactor
