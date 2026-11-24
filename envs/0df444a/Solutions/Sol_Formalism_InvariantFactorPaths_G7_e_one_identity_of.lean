-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.e_one_identity_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:46:31.311191+00:00
-- url     : https://prove2.me/submissions/0c993685-a04d-4427-a2c8-a1c342a154bc

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementAB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BiHomSum
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DegLESum
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_FinsuppStepInduction
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_hasseDir_zero_left
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_hasseDir_dirD
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_jetPair_linS_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_finsupp_step_induction
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_C_mul_left
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs


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
theorem _root_.solution : JetPairingHasseIdentity := by
  classical
  intro K ι κ _ _ _ b β
  induction β using finsupp_step_induction with
  | h0 =>
    intro Q G
    simp [hasseDir_zero_left]
  | hs β k ih =>
    intro Q G
    have h1 : (∏ k', linS (b k') ^ (β + Finsupp.single k 1 : κ →₀ ℕ) k') =
        linS (b k) * ∏ k', linS (b k') ^ β k' := by
      simp only [Finsupp.add_apply, pow_add, Finset.prod_mul_distrib]
      rw [mul_comm]
      congr 1
      rw [Finset.prod_eq_single k]
      · simp
      · intro k' _ hk'
        simp [hk'.symm]
      · intro h
        exact absurd (Finset.mem_univ k) h
    have h2 : (∏ k', ((β + Finsupp.single k 1 : κ →₀ ℕ) k').factorial) =
        (β k + 1) * ∏ k', (β k').factorial := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k),
        ← Finset.mul_prod_erase _ (fun k' => (β k').factorial) (Finset.mem_univ k)]
      have : ∏ k' ∈ Finset.univ.erase k, ((β + Finsupp.single k 1 : κ →₀ ℕ) k').factorial =
          ∏ k' ∈ Finset.univ.erase k, (β k').factorial :=
        Finset.prod_congr rfl fun j hj => by
          simp [(Finset.ne_of_mem_erase hj).symm]
      rw [this]
      simp only [Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
      ring
    rw [h1, mul_assoc, jetPair_linS_mul, ih, hasseDir_dirD, Formalism.DworkPowerSeriesWeights.jetPair_C_mul_left, h2]
    push_cast
    ring
end Formalism.InvariantFactorPaths.G7
