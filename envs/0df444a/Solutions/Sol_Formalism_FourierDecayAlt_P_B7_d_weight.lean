-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.d_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:12:53.665599+00:00
-- url     : https://prove2.me/submissions/3668573e-3f66-48a7-a396-24192394c313

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B7
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
namespace Formalism.FourierDecayAlt.P.B7
theorem _root_.solution (T T' s : ℝ) (hs : 0 < s) (q : (Fin r → ℂ) × ℂ) :
    bcWeight k r T T' (d_S r s q) = s ^ halfDimensionBlockSummand k r * bcWeight k r T T' q := by
  unfold bcWeight d_S
  dsimp only
  split_ifs with h
  · rw [← mul_assoc]
    congr 1
    rw [halfDimensionBlockSummand, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (pow_pos hs _), ← pow_mul]
  · simp
end Formalism.FourierDecayAlt.P.B7
