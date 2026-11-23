-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.biHom_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:54.345395+00:00
-- url     : https://prove2.me/submissions/7eeb7bb3-84ea-46f8-aef3-9de97a122fd0

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
variable {K ι κ : Type} [Field K] [Fintype κ]
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution {d e : ℕ} {F G : MvPolynomial κ (MvPolynomial ι K)} (hF : biHom d F)
    (hG : biHom e G) : biHom (d + e) (F * G) := by
  classical
  intro β n h
  rw [MvPolynomial.coeff_mul, MvPolynomial.coeff_sum] at h
  obtain ⟨x, hx, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [MvPolynomial.coeff_mul] at h
  obtain ⟨y, hy, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx hy
  have h1 := hF x.1 y.1 (left_ne_zero_of_mul h)
  have h2 := hG x.2 y.2 (right_ne_zero_of_mul h)
  rw [← hx, ← hy, map_add, map_add]
  omega
end Formalism.InvariantFactorPaths.G7
