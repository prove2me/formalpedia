-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.e_one_vanish_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:46:32.35934+00:00
-- url     : https://prove2.me/submissions/cf4741a1-85cf-4ba1-b13d-a79ad8a7c254

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementAB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BiHomSum
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DegLESum
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_FinsuppStepInduction
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_shiftPoly_one
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_hasseDir_mul

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
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution : HasseDerivProdVanish := by
  classical
  intro K ι κ _ _ b C
  induction C with
  | zero =>
    intro f m S _ β hβ
    have hne : (0 : κ →₀ ℕ) ≠ β := by
      rintro rfl
      simp at hβ
    simp only [Finset.univ_eq_empty, Finset.prod_empty, hasseDir, shiftPoly_one,
      MvPolynomial.coeff_one, if_neg hne]
  | succ C ih =>
    intro f m S h β hβ
    rw [Fin.prod_univ_succ, hasseDir_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    by_cases h0 : m 0 < ∑ k ∈ S, x.1 k
    · rw [h 0 x.1 h0, zero_mul]
    · rw [ih (fun c => f c.succ) (fun c => m c.succ) S (fun c => h c.succ) x.2, mul_zero]
      rw [Fin.sum_univ_succ, ← hx] at hβ
      simp only [Finsupp.add_apply, Finset.sum_add_distrib] at hβ
      omega
end Formalism.InvariantFactorPaths.G7
