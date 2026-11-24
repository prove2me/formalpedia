-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.d_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:04:47.615155+00:00
-- url     : https://prove2.me/submissions/707f8e05-054e-48b0-894f-3eeb0d354b79

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uw_block


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
namespace Formalism.FourierDecayAlt.P.B7
theorem _root_.solution (z : Fin (2 * r + k + 1) → ℂ) (t : ℝ) {h : Mat k r} (hh : h ∈ UWset k r z) :
    aDil k r t * h = h * aDil k r t := by
  have hb := WeylGroupFacts.uw_block hh
  ext i j
  rw [d_aDil_eq, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hi : i.val < r ∨ r + k < i.val
  · rw [hb.2 i j hi]
    by_cases hij : i = j
    · subst hij; simp [mul_comm]
    · simp [hij]
  · by_cases hj : j.val < r ∨ r + k < j.val
    · rw [hb.1 i j hj]
      by_cases hij : i = j
      · subst hij; simp [mul_comm]
      · simp [hij]
    · have e1 : d_dg k r t i = 1 := by
        unfold d_dg; rw [if_neg (by omega), if_pos (by omega)]
      have e2 : d_dg k r t j = 1 := by
        unfold d_dg; rw [if_neg (by omega), if_pos (by omega)]
      rw [e1, e2, one_mul, mul_one]
end Formalism.FourierDecayAlt.P.B7
