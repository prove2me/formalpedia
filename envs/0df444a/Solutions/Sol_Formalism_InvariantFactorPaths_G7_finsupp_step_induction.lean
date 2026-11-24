-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.finsupp_step_induction
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:25.201847+00:00
-- url     : https://prove2.me/submissions/18902ed2-4f30-4549-97ed-e1ce98484efb

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementAB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BiHomSum
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DegLESum
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_FinsuppStepInduction
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
theorem _root_.solution {κ : Type} (P : (κ →₀ ℕ) → Prop) (h0 : P 0)
    (hs : ∀ β k, P β → P (β + Finsupp.single k 1)) : ∀ β, P β := by
  classical
  intro β
  induction β using Finsupp.induction with
  | zero => exact h0
  | single_add a n f _ _ ih =>
    clear * - ih hs
    induction n with
    | zero => simpa using ih
    | succ n ihn =>
      have : Finsupp.single a (n + 1) + f = (Finsupp.single a n + f) + Finsupp.single a 1 := by
        rw [Finsupp.single_add]
        abel
      rw [this]
      exact hs _ _ ihn
end Formalism.InvariantFactorPaths.G7
