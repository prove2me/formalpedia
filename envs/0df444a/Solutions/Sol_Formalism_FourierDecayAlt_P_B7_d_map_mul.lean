-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.d_map_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:12:49.615329+00:00
-- url     : https://prove2.me/submissions/6e972d90-eebd-4830-8fd8-1b3b34e47431

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
theorem _root_.solution (ρ : ℝ) (hρ : 0 < ρ) :
    (volume : Measure ℂ).map (fun x => (ρ : ℂ) * x) = (Real.toNNReal ((ρ ^ 2)⁻¹)) • (volume : Measure ℂ) := by
  have h := Measure.map_addHaar_smul (volume : Measure ℂ) hρ.ne'
  rw [Complex.finrank_real_complex, abs_of_pos (by positivity)] at h
  have e : (fun x : ℂ => (ρ : ℂ) * x) = (ρ • ·) := by funext x; rw [Complex.real_smul]
  rw [e, h]; rfl
end Formalism.FourierDecayAlt.P.B7
