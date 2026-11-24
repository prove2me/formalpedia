-- Prove2me | solution 1 for Formalism.L2.Th1.D.UnramifiedCompletion.pow_pow_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:14:42.372354+00:00
-- url     : https://prove2.me/submissions/f381cd2e-69aa-47e1-8c43-8c6769198912

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_RingAFacts
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormRingALe
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_ExistsUnitFactorizationBounded

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
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.DworkPowerSeriesWeights (Unram)
open Formalism.L2.Th1.D.UnramifiedCompletion
variable (l : ℕ) [hl : Fact l.Prime]
variable {l}
namespace Formalism.L2.Th1.D.UnramifiedCompletion
theorem _root_.solution {M : Type*} [Monoid M] (x : M) (a : ℕ) (h : x ^ a = x) (k : ℕ) : x ^ (a ^ k) = x := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_mul, ih, h]
end Formalism.L2.Th1.D.UnramifiedCompletion
