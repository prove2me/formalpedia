-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.invF_meas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:56:30.888802+00:00
-- url     : https://prove2.me/submissions/65efab48-9253-4afd-8570-a051f393929b

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_det_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_adj_cont

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
theorem _root_.solution : Measurable (invF : (m → m → ℂ) → m → m → ℂ) := by
  have h : (invF : (m → m → ℂ) → m → m → ℂ) =
      fun g => ((((Matrix.of g).det)⁻¹ • (Matrix.of g).adjugate : Matrix m m ℂ) : m → m → ℂ) := by
    funext g
    simp only [invF, Matrix.inv_def, Ring.inverse_eq_inv']
    rfl
  rw [h]
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  exact det_cont.measurable.inv.mul (adj_cont.matrix_elem i j).measurable
end Formalism.FourierDecayAlt.P.HermitianFormFactor
