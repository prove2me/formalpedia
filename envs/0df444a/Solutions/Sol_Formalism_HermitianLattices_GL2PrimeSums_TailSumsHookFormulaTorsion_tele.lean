-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion.tele
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:33.083011+00:00
-- url     : https://prove2.me/submissions/7629eb04-3aa4-407c-99c1-b7f35813151d

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ExpNegLeDivPowFour

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GL2PrimeSums Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion
namespace Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion
theorem _root_.solution (g H : ℕ → ℝ) (M : ℕ) (h : ∀ n, M ≤ n → g (n + 1) ≤ H n - H (n + 1)) :
    ∀ N, M ≤ N → ∑ n ∈ Ioc M N, g n ≤ H M - H N := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    rw [Finset.sum_Ioc_succ_top hN]
    have := h N hN
    linarith
end Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion
