-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion.abel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:36.729842+00:00
-- url     : https://prove2.me/submissions/e3158bc3-8e64-4ad6-917f-561bc25aeb05

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
theorem _root_.solution (a : ℕ → ℂ) (M : ℕ) : ∀ N, M ≤ N →
    ∑ n ∈ Icc 1 N, a n / (n : ℂ) - ∑ n ∈ Icc 1 M, a n / (n : ℂ) =
      (∑ k ∈ Icc 1 N, a k) / ((N : ℂ) + 1) - (∑ k ∈ Icc 1 M, a k) / ((M : ℂ) + 1) +
        ∑ n ∈ Ioc M N, (∑ k ∈ Icc 1 n, a k) * (1 / (n : ℂ) - 1 / ((n : ℂ) + 1)) := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    rw [Finset.sum_Ioc_succ_top hN, Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
    have h1 : ((N : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N
    have h2 : ((N : ℂ) + 1 + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (N + 1)
    have e : ∑ n ∈ Icc 1 N, a n / (n : ℂ) = ∑ n ∈ Icc 1 M, a n / (n : ℂ) + ((∑ k ∈ Icc 1 N, a k) / ((N : ℂ) + 1) - (∑ k ∈ Icc 1 M, a k) / ((M : ℂ) + 1) +
        ∑ n ∈ Ioc M N, (∑ k ∈ Icc 1 n, a k) * (1 / (n : ℂ) - 1 / ((n : ℂ) + 1))) := by
      rw [← ih]; ring
    rw [e]
    push_cast
    field_simp
    ring
end Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion
