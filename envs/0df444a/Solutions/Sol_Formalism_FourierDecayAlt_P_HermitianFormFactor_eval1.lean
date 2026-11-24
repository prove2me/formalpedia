-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.eval1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:42:31.818228+00:00
-- url     : https://prove2.me/submissions/24dd9313-aa96-4dd8-bb04-33c38f4c3282

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Ff_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_act_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_inner1
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
theorem _root_.solution (F : Frame H Ep Em) (μ : Measure (m → m → ℂ)) [SFinite μ]
    (conc : ∀ᵐ g ∂μ, Matrix.of g ∈ UH H) (right : ∀ a ∈ UH H, μ.map (rmF a) = μ) (ρ : ℝ) :
    ∫⁻ g, (∫⁻ Y : Q → m → ℂ, Ff H Ep 1 Y * Ff H Ep ρ (act g Y)) ∂μ = Lv H Ep Q 1 * μ (Bset Ep Em ρ) := by
  rw [lintegral_lintegral_swap]
  · simp_rw [inner1 F μ conc right ρ]
    rw [lintegral_mul_const _ (Ff_meas 1)]; rfl
  · refine Measurable.aemeasurable ?_
    exact ((Ff_meas 1).comp measurable_snd).mul ((Ff_meas ρ).comp act_meas)
end Formalism.FourierDecayAlt.P.HermitianFormFactor
