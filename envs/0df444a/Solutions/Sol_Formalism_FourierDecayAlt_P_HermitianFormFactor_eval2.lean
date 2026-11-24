-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.eval2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:59:28.923248+00:00
-- url     : https://prove2.me/submissions/821e9d92-1559-49bc-b562-25e99f33ad95

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Ff_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_act_inv_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_inner2
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_swap_g
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
theorem _root_.solution (F : Frame H Ep Em) (hH : IsUnit H.det) (μ : Measure (m → m → ℂ)) [SFinite μ]
    (conc : ∀ᵐ g ∂μ, Matrix.of g ∈ UH H) (left : ∀ a ∈ UH H, μ.map (lmF a) = μ) (ρ : ℝ) :
    ∫⁻ g, (∫⁻ Y : Q → m → ℂ, Ff H Ep 1 Y * Ff H Ep ρ (act g Y)) ∂μ =
      Lv H Ep Q ρ * μ (invF ⁻¹' Bset Ep Em 1) := by
  have s1 : ∫⁻ g, (∫⁻ Y : Q → m → ℂ, Ff H Ep 1 Y * Ff H Ep ρ (act g Y)) ∂μ =
      ∫⁻ g, (∫⁻ Y : Q → m → ℂ, Ff H Ep 1 (act (invF g) Y) * Ff H Ep ρ Y) ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [conc] with g hg
    exact swap_g hH ρ hg
  rw [s1, lintegral_lintegral_swap]
  · simp_rw [inner2 F hH μ conc left ρ]
    rw [lintegral_const_mul _ (Ff_meas ρ), mul_comm]; rfl
  · refine Measurable.aemeasurable ?_
    exact ((Ff_meas 1).comp act_inv_meas).mul ((Ff_meas ρ).comp measurable_snd)
end Formalism.FourierDecayAlt.P.HermitianFormFactor
