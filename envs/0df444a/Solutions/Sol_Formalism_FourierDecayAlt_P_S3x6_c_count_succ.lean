-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x6.c_count_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:50:41.183508+00:00
-- url     : https://prove2.me/submissions/b41e1184-eab9-48db-b488-10b4d61287f1

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictOrthogonalComplementNondeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x6
open Module
variable {K : Type} [Field K] {σ : K →+* K}
open Finset
variable (K : Type) [Field K] [Fintype K] (q : ℕ)
namespace Formalism.FourierDecayAlt.P.S3x6
theorem _root_.solution [DecidableEq K] (n : ℕ) (c : K) :
    (univ.filter (fun w : Fin (n + 1) → K => ∑ i, w i ^ q * w i = c)).card =
      ∑ x : K, (univ.filter (fun w : Fin n → K => ∑ i, w i ^ q * w i = c - x ^ q * x)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun w => w 0) (t := univ) (fun _ _ => mem_univ _)]
  refine Finset.sum_congr rfl fun x _ => ?_
  symm
  refine Finset.card_bij (fun w _ => Fin.cons x w) ?_ ?_ ?_
  · intro w hw
    simp only [mem_filter, mem_univ, true_and] at hw ⊢
    refine ⟨?_, by simp⟩
    rw [Fin.sum_univ_succ]
    simp [hw]
  · intro w _ w' _ h
    funext i
    have h1 := congrFun h i.succ
    simpa using h1
  · intro w hw
    simp only [mem_filter, mem_univ, true_and] at hw
    refine ⟨Fin.tail w, ?_, ?_⟩
    · simp only [mem_filter, mem_univ, true_and]
      have h1 := hw.1
      rw [Fin.sum_univ_succ, hw.2] at h1
      rw [← h1]
      simp [Fin.tail]
    · rw [← hw.2]
      exact Fin.cons_self_tail w
end Formalism.FourierDecayAlt.P.S3x6
