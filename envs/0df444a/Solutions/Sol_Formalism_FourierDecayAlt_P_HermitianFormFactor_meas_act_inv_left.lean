-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.meas_act_inv_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:23:24.352841+00:00
-- url     : https://prove2.me/submissions/34268301-53c0-44a4-ad75-dbffd729da8b

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_invF_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_meas_act_left

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
theorem _root_.solution (ρ : ℝ) (Y : Q → m → ℂ) : Measurable fun g : m → m → ℂ => Ff H Ep ρ (act (invF g) Y) := by
  have key : ∀ φ : (m → m → ℂ) → m → m → ℂ, Measurable φ →
      Measurable fun g : m → m → ℂ => Ff H Ep ρ (act (φ g) Y) :=
    fun φ hφ => (meas_act_left ρ Y).comp hφ
  exact key invF invF_meas
end Formalism.FourierDecayAlt.P.HermitianFormFactor
