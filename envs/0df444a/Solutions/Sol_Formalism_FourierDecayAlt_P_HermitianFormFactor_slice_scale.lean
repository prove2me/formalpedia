-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.slice_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:22:49.726448+00:00
-- url     : https://prove2.me/submissions/355acef6-0bf9-4062-960a-7f9ba3de4d27

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Sl_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Sl_scale
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_finrank_QP
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Kf_slice
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Kf_slice_zero

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
open scoped Pointwise
namespace Formalism.FourierDecayAlt.P.HermitianFormFactor
theorem _root_.solution (T : Q → Q → ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∫⁻ B : Q → P → ℂ, Kf P Q ρ (T, B) =
      ENNReal.ofReal (ρ ^ (2 * Fintype.card P * Fintype.card Q)) * ∫⁻ B : Q → P → ℂ, Kf P Q 1 (T, B) := by
  by_cases hT : (Matrix.of T).PosDef ∧ (Matrix.trace (Matrix.of T)).re ≤ 1
  · rw [Kf_slice hT, Kf_slice hT, lintegral_indicator_one (Sl_meas T ρ), lintegral_indicator_one (Sl_meas T 1),
      Sl_scale hT.1 hρ, Measure.addHaar_smul, finrank_QP, abs_of_nonneg (pow_nonneg hρ _)]
  · simp [Kf_slice_zero hT]
end Formalism.FourierDecayAlt.P.HermitianFormFactor
