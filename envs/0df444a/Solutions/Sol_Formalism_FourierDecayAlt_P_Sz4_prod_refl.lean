-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz4.prod_refl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:39:41.59433+00:00
-- url     : https://prove2.me/submissions/1744d7fb-6495-4fa1-990e-24308c6e27b8

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz4
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz4
theorem _root_.solution (p : ℕ) : ∏ i ∈ Icc 1 p, (((p + 1 : ℕ) : ℝ) - (i : ℝ)) = (p.factorial : ℝ) := by
  have hf : ∀ n : ℕ, ∏ i ∈ Icc 1 n, (i : ℝ) = (n.factorial : ℝ) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.prod_Icc_succ_top (by omega), ih, Nat.factorial_succ]; push_cast; ring
  rw [← hf p]
  refine Finset.prod_nbij' (fun i => p + 1 - i) (fun i => p + 1 - i) ?_ ?_ ?_ ?_ ?_
  · intro i hi; simp only [mem_Icc] at hi ⊢; omega
  · intro i hi; simp only [mem_Icc] at hi ⊢; omega
  · intro i hi; simp only [mem_Icc] at hi; omega
  · intro i hi; simp only [mem_Icc] at hi; omega
  · intro i hi; simp only [mem_Icc] at hi; rw [Nat.cast_sub (by omega)]
end Formalism.FourierDecayAlt.P.Sz4
