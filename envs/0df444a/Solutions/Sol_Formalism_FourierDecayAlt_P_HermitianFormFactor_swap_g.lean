-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.swap_g
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:38:46.228942+00:00
-- url     : https://prove2.me/submissions/df33cffe-f3f7-4427-ba0e-a0f589991789

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_det_norm_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_mp_cols
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_UH_unit
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Ff_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_meas_act_right

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
theorem _root_.solution (hH : IsUnit H.det) (ρ : ℝ) {g : m → m → ℂ} (hg : Matrix.of g ∈ UH H) :
    ∫⁻ Y : Q → m → ℂ, Ff H Ep 1 Y * Ff H Ep ρ (act g Y) =
      ∫⁻ Y : Q → m → ℂ, Ff H Ep 1 (act (invF g) Y) * Ff H Ep ρ Y := by
  have hmp := mp_cols (Q := Q) (Matrix.of g) (det_norm_one hH hg)
  have hfm : Measurable (fun Y : Q → m → ℂ => Ff H Ep 1 (act (invF g) Y) * Ff H Ep ρ Y) :=
    (meas_act_right 1 (invF g)).mul (Ff_meas ρ)
  rw [← hmp.lintegral_comp hfm]
  refine lintegral_congr fun Y => ?_
  have : act (invF g) (fun j => Matrix.of g *ᵥ Y j) = Y := by
    funext j
    show (Matrix.of g)⁻¹ *ᵥ (Matrix.of g *ᵥ Y j) = Y j
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (UH_unit hH hg), Matrix.one_mulVec]
  rw [this]; rfl
end Formalism.FourierDecayAlt.P.HermitianFormFactor
