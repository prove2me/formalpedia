-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.Kg_meas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:45:36.375072+00:00
-- url     : https://prove2.me/submissions/11d13145-0722-48cf-938b-7bba89f80c57

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Kf_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_gramF_cont

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
theorem _root_.solution (ρ : ℝ) : Measurable (fun p : (Q → Q → ℂ) × (Q → P → ℂ) => Kf P Q ρ (gramF p.1, p.2)) := by
  have h : Measurable (fun p : (Q → Q → ℂ) × (Q → P → ℂ) => (gramF p.1, p.2)) :=
    Measurable.prod (f := fun p : (Q → Q → ℂ) × (Q → P → ℂ) => (gramF p.1, p.2))
      (gramF_cont.measurable.comp measurable_fst) measurable_snd
  exact (Kf_meas ρ).comp h
end Formalism.FourierDecayAlt.P.HermitianFormFactor
