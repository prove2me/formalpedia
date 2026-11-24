-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.jetPair_X_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:48:19.913317+00:00
-- url     : https://prove2.me/submissions/25008810-bb03-4456-a0db-4ef44e8224f6

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementAB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BiHomSum
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DegLESum
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_FinsuppStepInduction
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_jetPair_monomial_left
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_add_left
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_mfact_add_single
import Theorems.Thm_Formalism_FG_InjVAux_HasOrd_add
import Theorems.Thm_Formalism_FG_InvIntVAux_Low_add


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
variable {K ι : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution (Q : MvPolynomial ι K) (x : ι) (G : MvPowerSeries ι K) :
    jetPair Q (MvPowerSeries.X x * G) = jetPair (MvPolynomial.pderiv x Q) G := by
  classical
  induction Q using MvPolynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, Formalism.DworkPowerSeriesWeights.jetPair_add_left, Formalism.DworkPowerSeriesWeights.jetPair_add_left, hp, hq]
  | monomial κ a =>
    rw [MvPolynomial.pderiv_monomial, jetPair_monomial_left, jetPair_monomial_left]
    by_cases h : κ x = 0
    · rw [h]
      have : MvPowerSeries.coeff κ (MvPowerSeries.X x * G) = 0 := by
        rw [MvPowerSeries.X, MvPowerSeries.coeff_monomial_mul, if_neg]
        intro hle
        have := hle x
        simp [h] at this
      rw [this]
      simp
    · obtain ⟨μ, rfl⟩ : ∃ μ, κ = μ + Finsupp.single x 1 := by
        refine ⟨κ - Finsupp.single x 1, ?_⟩
        rw [tsub_add_cancel_of_le]
        rw [Finsupp.single_le_iff]
        omega
      rw [add_tsub_cancel_right, Formalism.DworkPowerSeriesWeights.mfact_add_single, add_comm μ, MvPowerSeries.X,
        MvPowerSeries.coeff_add_monomial_mul]
      simp only [Finsupp.add_apply, Finsupp.single_eq_same, Nat.cast_mul, Nat.cast_add,
        Nat.cast_one, one_mul]
      ring
end Formalism.InvariantFactorPaths.G7
