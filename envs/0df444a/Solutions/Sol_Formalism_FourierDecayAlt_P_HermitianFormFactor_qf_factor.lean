-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.qf_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:01:24.190408+00:00
-- url     : https://prove2.me/submissions/7208f6c6-4cf7-4a91-a7fd-68c91929b995

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_trace_re

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
theorem _root_.solution {T a : Matrix Q Q ℂ} (h : T⁻¹ = aᴴ * a) (B : Matrix P Q ℂ) :
    qf T B = ∑ i, ∑ j, Complex.normSq ((B * aᴴ) i j) := by
  unfold qf
  rw [h, show B * (aᴴ * a) * Bᴴ = (B * aᴴ) * (B * aᴴ)ᴴ by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc], trace_re]
end Formalism.FourierDecayAlt.P.HermitianFormFactor
