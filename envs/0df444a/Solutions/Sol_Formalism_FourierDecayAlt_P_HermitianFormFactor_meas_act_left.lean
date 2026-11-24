-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.meas_act_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:03:15.971839+00:00
-- url     : https://prove2.me/submissions/8295f70f-9959-43bc-8504-0bff0efb549f

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_of_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Ff_meas

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
theorem _root_.solution (ρ : ℝ) (Y : Q → m → ℂ) : Measurable fun g : m → m → ℂ => Ff H Ep ρ (act g Y) := by
  unfold act
  exact (Ff_meas ρ).comp (continuous_pi fun j => of_cont.matrix_mulVec continuous_const).measurable
end Formalism.FourierDecayAlt.P.HermitianFormFactor
