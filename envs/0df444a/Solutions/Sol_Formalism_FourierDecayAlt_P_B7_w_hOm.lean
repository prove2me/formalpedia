-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.w_hOm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:34:46.005891+00:00
-- url     : https://prove2.me/submissions/13e4bdf6-dea1-44a0-8ffa-e0075059790a

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
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
attribute [local instance] sfG sfW sfN sfW' sfSS properFD
namespace Formalism.FourierDecayAlt.P.B7
theorem _root_.solution (D : RealPlaceData k r Wp Wq) (w₁ w₂ : ℝ → ℝ) (p : SS k r) :
    (∫ τ : ℝ × ℝ, ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * xiTau D τ p) = Om D w₁ w₂ p := by
  have e : ∀ τ : ℝ × ℝ, ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * xiTau D τ p =
      ((w₁ τ.1 : ℂ) * Complex.exp (Complex.I * ((τ.1 * lam k r D.z (Matrix.of p.1.2) : ℝ) : ℂ))) *
      ((w₂ τ.2 : ℂ) * Complex.exp (Complex.I * ((τ.2 * -lam k r D.z' (Matrix.of p.2.2) : ℝ) : ℂ))) := by
    intro τ
    rw [xiTau, mul_mul_mul_comm, ← Complex.exp_add]
    have h : Complex.I * (((τ.1 * lam k r D.z (Matrix.of p.1.2) - τ.2 * lam k r D.z' (Matrix.of p.2.2) : ℝ)) : ℂ) =
        Complex.I * ((τ.1 * lam k r D.z (Matrix.of p.1.2) : ℝ) : ℂ) +
          Complex.I * ((τ.2 * -lam k r D.z' (Matrix.of p.2.2) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [h]
    simp only [Complex.ofReal_mul]
  simp_rw [e]
  rw [Measure.volume_eq_prod]
  exact integral_prod_mul (fun t : ℝ => (w₁ t : ℂ) * Complex.exp (Complex.I * ((t * lam k r D.z (Matrix.of p.1.2) : ℝ) : ℂ)))
    (fun t : ℝ => (w₂ t : ℂ) * Complex.exp (Complex.I * ((t * -lam k r D.z' (Matrix.of p.2.2) : ℝ) : ℂ)))
end Formalism.FourierDecayAlt.P.B7
