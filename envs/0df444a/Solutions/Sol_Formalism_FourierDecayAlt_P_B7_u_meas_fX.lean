-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.u_meas_fX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:57:54.280585+00:00
-- url     : https://prove2.me/submissions/0aebff14-9c3e-4472-8ecc-320f7b149e3d

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_continuous_lam
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_meas_mulM

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
theorem _root_.solution (z : Fin (2 * r + k + 1) → ℂ) {Ξ : Mat k r → NNReal}
    (hΞ : Measurable fun x : Mt k r => Ξ (Matrix.of x)) : Measurable (u_fX z Ξ) := by
  unfold u_fX
  have hm : Measurable fun p : Mt k r × Mt k r => mulM p.2 p.1 := meas_mulM measurable_snd measurable_fst
  have h1 : Measurable fun p : Mt k r × Mt k r => Ξ (Matrix.of (mulM p.2 p.1)) := hΞ.comp hm
  have h1' : Measurable fun p : Mt k r × Mt k r => ((Ξ (Matrix.of p.2 * Matrix.of p.1) : NNReal) : ℝ≥0∞) :=
    h1.coe_nnreal_ennreal
  have hl : Measurable fun p : Mt k r × Mt k r => lam k r z (Matrix.of p.2) :=
    (continuous_lam z).measurable.comp measurable_snd
  have h2 : Measurable fun p : Mt k r × Mt k r => (1 + |lam k r z (Matrix.of p.2)|) ^ (-(2 : ℝ)) :=
    (measurable_const.add (continuous_abs.measurable.comp hl)).pow_const _
  exact h1'.mul h2.ennreal_ofReal
end Formalism.FourierDecayAlt.P.B7
