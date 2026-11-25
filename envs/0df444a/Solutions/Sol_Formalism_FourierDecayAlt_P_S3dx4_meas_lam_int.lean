-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3dx4.meas_lam_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:38:02.494933+00:00
-- url     : https://prove2.me/submissions/cbb6668d-160c-434a-a592-c2cc878ec0dd

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousSandwichedProduct
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeasurableEnormComposition
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_meas_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_measurable_enorm_composition
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_meas_hn
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_meas_matmul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3dx4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.S3dx4
theorem _root_.solution {e0 : Mx k r → ℂ} (he0 : Continuous e0) (γ : Mx k r) {α : Type*} [MeasurableSpace α]
    {X Y : α → Formalism.QuantumDeterminants.Mt k r} {P Q : α → Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r}
    (hX : Measurable X) (hY : Measurable Y) (hP : Measurable P) (hQ : Measurable Q) :
    Measurable (fun t => ‖e0 ((Matrix.of (X t))⁻¹ * (Matrix.of (P t).1 * Matrix.of (P t).2) * γ *
      (Matrix.of (Q t).1 * Matrix.of (Q t).2)⁻¹ * Matrix.of (Y t))‖ₑ) := by
  have mγ : Measurable (fun _ : α => (Matrix.of.symm γ : Formalism.QuantumDeterminants.Mt k r)) := measurable_const
  have M := meas_matmul (meas_matmul (meas_matmul (meas_matmul (meas_inv hX) (meas_hn hP)) mγ)
    (meas_inv (meas_hn hQ))) hY
  exact measurable_enorm_composition he0 M
end Formalism.FourierDecayAlt.P.S3dx4
