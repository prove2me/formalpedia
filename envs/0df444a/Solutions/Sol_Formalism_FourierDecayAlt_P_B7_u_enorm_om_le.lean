-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.u_enorm_om_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:12:56.095791+00:00
-- url     : https://prove2.me/submissions/5760c5f3-7749-40cd-b030-8af4604f637e

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_FourierDecayAlt_P_test_function_decay


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
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
attribute [local instance] sfG sfW sfN sfW' sfSS properFD
namespace Formalism.FourierDecayAlt.P.B7
theorem _root_.solution {w : ℝ → ℝ} (h : IsTest w) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ x : ℝ, ‖om w x‖ₑ ≤ K * ENNReal.ofReal ((1 + |x|) ^ (-(2 : ℝ))) := by
  obtain ⟨C, hC⟩ := test_function_decay w h
  refine ⟨ENNReal.ofReal C, ENNReal.ofReal_ne_top, fun x => ?_⟩
  have hpos : (0 : ℝ) ≤ 1 + |x| := by positivity
  have e : ((1 + |x|) ^ 2)⁻¹ = (1 + |x|) ^ (-(2 : ℝ)) := by
    rw [Real.rpow_neg hpos, Real.rpow_two]
  rw [← ofReal_norm, ← ENNReal.ofReal_mul' (by positivity), ← e]
  exact ENNReal.ofReal_le_ofReal (hC x)
end Formalism.FourierDecayAlt.P.B7
