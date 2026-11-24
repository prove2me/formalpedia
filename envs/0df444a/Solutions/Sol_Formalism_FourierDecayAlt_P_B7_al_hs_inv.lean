-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.al_hs_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:34:54.75408+00:00
-- url     : https://prove2.me/submissions/36eb481c-a208-4a9e-89cb-93bd372cbdce

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_al_sum_inner

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
theorem _root_.solution (U : Wp →L[ℂ] Wp) (hU : ∀ v, ‖U v‖ = ‖v‖) (V : Wq →L[ℂ] Wq) (hV : ∀ v, ‖V v‖ = ‖v‖)
    (A B : Wq →L[ℂ] Wp) :
    inner ℂ (hsVec (U.comp (A.comp V))) (hsVec (U.comp (B.comp V))) = inner ℂ (hsVec A) (hsVec B) := by
  let lU : Wp →ₗᵢ[ℂ] Wp := ⟨U.toLinearMap, hU⟩
  let lV : Wq →ₗᵢ[ℂ] Wq := ⟨V.toLinearMap, hV⟩
  let eV : Wq ≃ₗᵢ[ℂ] Wq := lV.toLinearIsometryEquiv rfl
  have h1 : inner ℂ (hsVec (U.comp (A.comp V))) (hsVec (U.comp (B.comp V))) =
      ∑ i, inner ℂ (A (((stdOrthonormalBasis ℂ Wq).map eV) i)) (B (((stdOrthonormalBasis ℂ Wq).map eV) i)) := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [OrthonormalBasis.map_apply]
    exact lU.inner_map_map _ _
  have h2 : inner ℂ (hsVec A) (hsVec B) =
      ∑ i, inner ℂ (A ((stdOrthonormalBasis ℂ Wq) i)) (B ((stdOrthonormalBasis ℂ Wq) i)) := by
    rw [PiLp.inner_apply]
    rfl
  rw [h1, h2, al_sum_inner, al_sum_inner]
end Formalism.FourierDecayAlt.P.B7
