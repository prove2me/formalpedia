-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.al_lam_tr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:08:40.334145+00:00
-- url     : https://prove2.me/submissions/6cb46463-2a05-4e28-8cc3-0268b4d7c803

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_QuantumDeterminants_length_additive_holds
import Theorems.Thm_Formalism_QuantumDeterminants_unitary_weyl_normal_holds


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
theorem _root_.solution (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) {h n₁ n : Mat k r} (hh : h ∈ UWset k r z)
    (hn₁ : n₁ ∈ Nset k r) (hn : n ∈ Nset k r) :
    lam k r z (n₁ * (h * n * h⁻¹)) = lam k r z n₁ + lam k r z n := by
  have hc := unitary_weyl_normal_holds k r z hz h hh n hn
  unfold lam
  rw [length_additive_holds k r z hz n₁ hn₁ _ hc.1, hc.2, mul_add, Complex.add_re]
end Formalism.FourierDecayAlt.P.B7
