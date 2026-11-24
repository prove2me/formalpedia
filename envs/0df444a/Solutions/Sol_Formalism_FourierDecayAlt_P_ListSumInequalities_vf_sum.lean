-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ListSumInequalities.vf_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:57:57.447176+00:00
-- url     : https://prove2.me/submissions/433b730b-9e82-453d-b221-2deb4d01037a

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DerivativeRulesA1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExponentWordRecursion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ListSumInequalities
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10 Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.ListSumInequalities
theorem _root_.solution (b : Bool) {ι : Type*} (s : Finset ι) (c : ι → ℝ) (Y : ι → Mat k r) (g : Mat k r) :
    vf b (∑ i ∈ s, c i • Y i) g = ∑ i ∈ s, c i • vf b (Y i) g := by
  cases b <;> simp [vf, mulL, mulR, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
end Formalism.FourierDecayAlt.P.ListSumInequalities
