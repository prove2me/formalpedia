-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.degLE_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:13.209942+00:00
-- url     : https://prove2.me/submissions/f3d19e88-a62c-4980-873d-8ba7628e0f0c

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementAB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BiHomSum
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DegLESum
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_FinsuppStepInduction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (jetPair)
variable {κ R : Type} [CommRing R]
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution {W : Finset κ} {n m : ℕ} {F G : MvPolynomial κ R} (hF : degLE W n F)
    (hG : degLE W m G) : degLE W (n + m) (F * G) := by
  classical
  intro β h
  rw [MvPolynomial.coeff_mul] at h
  obtain ⟨x, hx, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  have h1 := hF x.1 (left_ne_zero_of_mul h)
  have h2 := hG x.2 (right_ne_zero_of_mul h)
  rw [← hx]
  simp only [Finsupp.add_apply, Finset.sum_add_distrib]
  omega
end Formalism.InvariantFactorPaths.G7
