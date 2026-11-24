-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.Mv_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:45:43.711746+00:00
-- url     : https://prove2.me/submissions/ae5dbeec-034d-4e56-8fce-20a4b9658e33

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_gram_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Kf_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_slice_scale

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
theorem _root_.solution {ρ : ℝ} (hρ : 0 ≤ ρ) :
    Mv P Q ρ = ENNReal.ofReal (ρ ^ (2 * Fintype.card P * Fintype.card Q)) * Mv P Q 1 := by
  have hK : Measurable (fun p : (Q → Q → ℂ) × (Q → P → ℂ) => Kf P Q 1 (gramF p.1, p.2)) := by
    have hg : Measurable (fun X : Q → Q → ℂ => fun i j => gram X i j) :=
      measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => (gram_cont.matrix_elem i j).measurable
    have h : Measurable (fun p : (Q → Q → ℂ) × (Q → P → ℂ) => (gramF p.1, p.2)) :=
      Measurable.prod (f := fun p : (Q → Q → ℂ) × (Q → P → ℂ) => (gramF p.1, p.2)) (hg.comp measurable_fst) measurable_snd
    exact (Kf_meas 1).comp h
  unfold Mv
  simp_rw [slice_scale _ hρ]
  rw [lintegral_const_mul _ hK.lintegral_prod_right']
end Formalism.FourierDecayAlt.P.HermitianFormFactor
