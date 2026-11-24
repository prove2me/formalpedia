-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.qf_meas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:39:28.545182+00:00
-- url     : https://prove2.me/submissions/a9059414-f539-4104-9d8a-165905117c17

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_det_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_adj_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_cm_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_qf_eq

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
theorem _root_.solution : Measurable (fun p : (Q → Q → ℂ) × (Q → P → ℂ) => qf (Matrix.of p.1) (cm p.2)) := by
  have h : (fun p : (Q → Q → ℂ) × (Q → P → ℂ) => qf (Matrix.of p.1) (cm p.2)) =
      fun p => (((Matrix.of p.1).det)⁻¹ * Matrix.trace (cm p.2 * (Matrix.of p.1).adjugate * (cm p.2)ᴴ)).re :=
    funext fun p => qf_eq _ _
  rw [h]
  have hB : Continuous (fun p : (Q → Q → ℂ) × (Q → P → ℂ) => cm p.2) := cm_cont.comp continuous_snd
  have htr : Continuous (fun p : (Q → Q → ℂ) × (Q → P → ℂ) =>
      Matrix.trace (cm p.2 * (Matrix.of p.1).adjugate * (cm p.2)ᴴ)) :=
    ((hB.matrix_mul (adj_cont.comp continuous_fst)).matrix_mul hB.matrix_conjTranspose).matrix_trace
  exact Complex.measurable_re.comp ((det_cont.comp continuous_fst).measurable.inv.mul htr.measurable)
end Formalism.FourierDecayAlt.P.HermitianFormFactor
