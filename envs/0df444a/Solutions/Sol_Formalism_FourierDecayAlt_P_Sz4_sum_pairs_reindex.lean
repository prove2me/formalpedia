-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz4.sum_pairs_reindex
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:39.541126+00:00
-- url     : https://prove2.me/submissions/5d3bf05c-8739-4cf4-b9ce-d89c494f6b01

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
theorem _root_.solution (J : ℕ) (F : ℕ → ℕ → ℝ) :
    ∑ i ∈ Icc 1 J, ∑ j ∈ Ioc i J, F i j =
      ∑ d ∈ Ioc 0 J, ∑ i ∈ Icc 1 (J - d), F i (i + d) := by
  have h1 : ∀ i ∈ Icc 1 J, ∑ j ∈ Ioc i J, F i j = ∑ d ∈ Ioc 0 (J - i), F i (i + d) := by
    intro i hi
    rw [mem_Icc] at hi
    refine Finset.sum_nbij' (fun j => j - i) (fun d => i + d) ?_ ?_ ?_ ?_ ?_
    · intro j hj; simp only [mem_Ioc] at hj ⊢; omega
    · intro d hd; simp only [mem_Ioc] at hd ⊢; omega
    · intro j hj; simp only [mem_Ioc] at hj; omega
    · intro d hd; omega
    · intro j hj; simp only [mem_Ioc] at hj; congr 1; omega
  rw [Finset.sum_congr rfl h1]
  refine Finset.sum_comm' ?_
  intro i d
  simp only [mem_Icc, mem_Ioc]
  omega
end Formalism.FourierDecayAlt.P.Sz4
