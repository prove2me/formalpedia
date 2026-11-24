-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.asm_num
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:48.850389+00:00
-- url     : https://prove2.me/submissions/6bfba22b-8867-4223-a5ea-3cf80e4cd998

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LevelLatticeOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.KP Formalism.InvariantFactorPaths.KP.LL
open Formalism.GM
open MvPolynomial Finset Formalism.GM.M
namespace Formalism.InvariantFactorPaths.KP.LL
theorem _root_.solution (p : ℕ) [Fact p.Prime] (a r : ℕ) (ha : 1 ≤ a) :
    r * Nat.log p (2 * a) + Nat.log p (6 * a + r) ≤ ⌈((r : ℝ) + 1) * lgV2 p a r⌉₊ := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have h1 : (Nat.log p (2 * a) : ℝ) ≤ Real.logb p (8 * a + r) := by
    refine (Real.natLog_le_logb _ _).trans ?_
    apply Real.logb_le_logb_of_le hp
    · push_cast; linarith
    · push_cast; linarith
  have h2 : (Nat.log p (6 * a + r) : ℝ) ≤ Real.logb p (8 * a + r) := by
    refine (Real.natLog_le_logb _ _).trans ?_
    apply Real.logb_le_logb_of_le hp
    · push_cast; linarith
    · push_cast; linarith
  have h3 : ((r * Nat.log p (2 * a) + Nat.log p (6 * a + r) : ℕ) : ℝ) ≤ ((r : ℝ) + 1) * lgV2 p a r := by
    push_cast
    unfold lgV2
    have := mul_le_mul_of_nonneg_left h1 hr
    nlinarith
  exact_mod_cast h3.trans (Nat.le_ceil _)
end Formalism.InvariantFactorPaths.KP.LL
