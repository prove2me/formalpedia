-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.act_inv_meas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:59:28.671168+00:00
-- url     : https://prove2.me/submissions/6834f8b1-a3dc-47a2-8e47-c2440ea08c72

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_invF_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_act_meas

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
theorem _root_.solution : Measurable (fun p : (m → m → ℂ) × (Q → m → ℂ) => act (invF p.1) p.2) := by
  have key : ∀ φ : (m → m → ℂ) → m → m → ℂ, Measurable φ →
      Measurable (fun p : (m → m → ℂ) × (Q → m → ℂ) => act (φ p.1) p.2) := by
    intro φ hφ
    have hp : Measurable (fun p : (m → m → ℂ) × (Q → m → ℂ) => (φ p.1, p.2)) :=
      Measurable.prod (f := fun p : (m → m → ℂ) × (Q → m → ℂ) => (φ p.1, p.2)) (hφ.comp measurable_fst) measurable_snd
    exact act_meas.comp hp
  exact key invF invF_meas
end Formalism.FourierDecayAlt.P.HermitianFormFactor
