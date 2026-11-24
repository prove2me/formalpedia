-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.qf_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:40:59.673296+00:00
-- url     : https://prove2.me/submissions/60b7cd5a-6b01-4474-8d33-8ec140d6ffe5

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_cm_smul

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
theorem _root_.solution (T : Matrix Q Q ℂ) (c : ℝ) (B : Q → P → ℂ) : qf T (cm (c • B)) = c ^ 2 * qf T (cm B) := by
  unfold qf
  rw [cm_smul]
  simp only [Matrix.smul_mul, Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.trace_smul, smul_smul,
    smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
  rw [← Complex.ofReal_mul, Complex.re_ofReal_mul, sq]
end Formalism.FourierDecayAlt.P.HermitianFormFactor
