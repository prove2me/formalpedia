-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.qf_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:18:17.014121+00:00
-- url     : https://prove2.me/submissions/206cebc8-8585-43d7-af6b-f80ffdb776f9

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor

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
theorem _root_.solution (T : Matrix Q Q ℂ) (B : Matrix P Q ℂ) :
    qf T B = ((T.det)⁻¹ * Matrix.trace (B * T.adjugate * Bᴴ)).re := by
  unfold qf
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
end Formalism.FourierDecayAlt.P.HermitianFormFactor
