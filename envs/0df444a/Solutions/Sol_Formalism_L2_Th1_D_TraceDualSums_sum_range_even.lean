-- Prove2me | solution 1 for Formalism.L2.Th1.D.TraceDualSums.sum_range_even
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:47:19.394472+00:00
-- url     : https://prove2.me/submissions/f563a7e7-5a0d-41a3-8fa7-ec285c139171

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionHypothesesOfLevelOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementK
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_TraceDualExists

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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.InvariantFactorPaths.G7 (UnrOK)
open Formalism.L2.Th1.D.TraceDualSums
namespace Formalism.L2.Th1.D.TraceDualSums
theorem _root_.solution {M : Type} [AddCommMonoid M] (m : ℕ) (g : ℕ → M) :
    (∑ i ∈ Finset.range (2 * m), if i % 2 = 0 then g i else 0) =
      ∑ k ∈ Finset.range m, g (2 * k) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    have h1 : (2 * m) % 2 = 0 := by omega
    have h2 : ¬ (2 * m + 1) % 2 = 0 := by omega
    rw [if_pos h1, if_neg h2, add_zero]
end Formalism.L2.Th1.D.TraceDualSums
