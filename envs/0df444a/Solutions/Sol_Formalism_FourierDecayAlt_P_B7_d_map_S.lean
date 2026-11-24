-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.d_map_S
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:54:04.37107+00:00
-- url     : https://prove2.me/submissions/38430923-d673-4346-8732-af170d3379e3

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_map_volume_triangular_scaling

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
    (volume : Measure ((Fin r → ℂ) × ℂ)).map (d_S r s) =
      ENNReal.ofReal ((s ^ halfDimensionRankTwoSummand r)⁻¹) • (volume : Measure ((Fin r → ℂ) × ℂ)) := by
  have e : d_S r s = Prod.map (fun (c : Fin r → ℂ) a => ((s ^ (r - a.val) : ℝ) : ℂ) * c a) id := rfl
  have m1 : Measurable (fun (c : Fin r → ℂ) a => ((s ^ (r - a.val) : ℝ) : ℂ) * c a) :=
    measurable_pi_iff.2 fun a => (continuous_const.mul (continuous_apply a)).measurable
  have hc : (∏ a : Fin r, Real.toNNReal (((s ^ (r - a.val)) ^ 2)⁻¹)) = Real.toNNReal ((s ^ halfDimensionRankTwoSummand r)⁻¹) := by
    rw [← Real.toNNReal_prod_of_nonneg (fun a _ => by positivity)]
    congr 1
    unfold halfDimensionRankTwoSummand
    rw [Finset.prod_inv_distrib, ← Finset.prod_pow_eq_pow_sum]
    simp only [pow_mul]
  rw [e, Measure.volume_eq_prod, ← Measure.map_prod_map _ _ m1 measurable_id, map_volume_triangular_scaling s hs, Measure.map_id,
    Measure.prod_smul_left, hc]
  rfl
end Formalism.FourierDecayAlt.P.B7
