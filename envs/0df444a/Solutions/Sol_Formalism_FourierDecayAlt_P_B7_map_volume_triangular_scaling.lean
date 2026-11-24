-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.map_volume_triangular_scaling
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:32:31.338392+00:00
-- url     : https://prove2.me/submissions/3dabaa06-8c92-4515-92f9-f744e22ef5c8

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_d_pi_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_d_map_mul

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
theorem _root_.solution (s : ℝ) (hs : 0 < s) :
    (volume : Measure (Fin r → ℂ)).map (fun c a => ((s ^ (r - a.val) : ℝ) : ℂ) * c a) =
      (∏ a : Fin r, Real.toNNReal (((s ^ (r - a.val)) ^ 2)⁻¹)) • (volume : Measure (Fin r → ℂ)) := by
  have h := measurePreserving_pi (fun _ : Fin r => (volume : Measure ℂ))
    (fun a : Fin r => (Real.toNNReal (((s ^ (r - a.val)) ^ 2)⁻¹)) • (volume : Measure ℂ))
    (f := fun a x => ((s ^ (r - a.val) : ℝ) : ℂ) * x)
    (fun a => ⟨(continuous_const.mul continuous_id).measurable, d_map_mul _ (by positivity)⟩)
  rw [volume_pi, h.map_eq, d_pi_smul]
end Formalism.FourierDecayAlt.P.B7
