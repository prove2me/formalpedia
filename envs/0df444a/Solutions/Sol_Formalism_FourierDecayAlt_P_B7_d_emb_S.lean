-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.d_emb_S
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:08:12.764345+00:00
-- url     : https://prove2.me/submissions/ccf1026d-0f64-412f-bef8-f4c37b0ad2d5

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
theorem _root_.solution (s : ℝ) (hs : 0 < s) : MeasurableEmbedding (d_S r s) := by
  have hs0 : s ≠ 0 := hs.ne'
  have hm : ∀ u : ℝ, Measurable (d_S r u) := fun u => by
    show Measurable fun q : (Fin r → ℂ) × ℂ => ((fun a : Fin r => ((u ^ (r - a.val) : ℝ) : ℂ) * q.1 a), q.2)
    first
      | fun_prop
      | exact (by fun_prop : Continuous fun q : (Fin r → ℂ) × ℂ => ((fun a : Fin r => ((u ^ (r - a.val) : ℝ) : ℂ) * q.1 a), q.2)).measurable
      | measurability
  have key : ∀ (u v : ℝ), u * v = 1 → ∀ q, d_S r u (d_S r v q) = q := by
    intro u v huv q
    refine Prod.ext (funext fun a => ?_) rfl
    show ((u ^ (r - a.val) : ℝ) : ℂ) * (((v ^ (r - a.val) : ℝ) : ℂ) * q.1 a) = q.1 a
    rw [← mul_assoc, ← Complex.ofReal_mul, ← mul_pow, huv, one_pow, Complex.ofReal_one, one_mul]
  refine MeasurableEmbedding.of_measurable_inverse (hm s) ?_ (hm s⁻¹) (key s⁻¹ s (inv_mul_cancel₀ hs0))
  have : Set.range (d_S r s) = Set.univ := Set.eq_univ_of_forall fun q => ⟨_, key s s⁻¹ (mul_inv_cancel₀ hs0) q⟩
  rw [this]
  exact MeasurableSet.univ
end Formalism.FourierDecayAlt.P.B7
