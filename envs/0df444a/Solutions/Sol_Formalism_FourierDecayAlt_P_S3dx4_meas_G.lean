-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3dx4.meas_G
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:30:35.986268+00:00
-- url     : https://prove2.me/submissions/fedc4e75-c4d5-4145-8f5f-457ba3f839e4

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InnerBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TripleIntegrandMeasurable
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x1_invM_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_invM_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_gN_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_meas_matmul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_mt_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_invM_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_NInt_gN_cont


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
theorem _root_.solution (γ : Mx k r) (b : ℝ) :
    Measurable (fun pp : B.SS k r =>
      ‖B.gN (Matrix.of pp.1.1 * Matrix.of pp.1.2 * γ * (Matrix.of pp.2.2)⁻¹ * (Matrix.of pp.2.1)⁻¹) ^ (-b)‖ₑ) := by
  have hi := B2x1.invM_meas (k := k) (r := r)
  have m1 : Measurable (fun pp : B.SS k r => pp.1.1) := measurable_fst.fst
  have m2 : Measurable (fun pp : B.SS k r => pp.1.2) := measurable_fst.snd
  have m3 : Measurable (fun pp : B.SS k r => B2.invM pp.2.2) := hi.comp measurable_snd.snd
  have m4 : Measurable (fun pp : B.SS k r => B2.invM pp.2.1) := hi.comp measurable_snd.fst
  have mγ : Measurable (fun _ : B.SS k r => (Matrix.of.symm γ : Formalism.QuantumDeterminants.Mt k r)) := measurable_const
  have M := meas_matmul (meas_matmul (meas_matmul (meas_matmul m1 m2) mγ) m3) m4
  have hg : Continuous (fun y : Formalism.QuantumDeterminants.Mt k r => B.gN (Matrix.of y)) := gN_cont.comp mt_cont
  exact ((hg.measurable.comp M).pow_const (-b)).enorm
end Formalism.FourierDecayAlt.P.S3dx4
