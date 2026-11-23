-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Markov.exists_rot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:29:14.521495+00:00
-- url     : https://prove2.me/submissions/fc0142d3-6b31-4254-b1c3-c858012ba191

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Markov
import Theorems.Thm_Formalism_FourierDecayAlt_P_Markov_rot_eval
import Theorems.Thm_Formalism_FourierDecayAlt_P_Markov_rot_natDegree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Markov
open Polynomial Real Finset
namespace Formalism.FourierDecayAlt.P.Markov
theorem _root_.solution (a b : ℝ) (p : ℝ[X]) (n : ℕ) (hn : n ≠ 0) (hp : p.natDegree ≤ n) :
    ∃ A B : ℝ[X], B.degree < n ∧ ∀ y z : ℝ, y ^ 2 + z ^ 2 = 1 →
      p.eval (a * y + b * z) = A.eval y + z * B.eval y := by
  refine ⟨∑ m ∈ Finset.range (n + 1), C (p.coeff m) * (rot a b m).1,
    ∑ m ∈ Finset.range (n + 1), C (p.coeff m) * (rot a b m).2, ?_, ?_⟩
  · have h : (∑ m ∈ Finset.range (n + 1), C (p.coeff m) * (rot a b m).2).natDegree ≤ n - 1 := by
      refine natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
      refine (natDegree_C_mul_le _ _).trans ?_
      rcases m with _ | m
      · simp [rot]
      · have := (rot_natDegree a b m).2.1
        have := Finset.mem_range.mp hm
        omega
    refine lt_of_le_of_lt (degree_le_of_natDegree_le h) ?_
    exact_mod_cast Nat.sub_lt (Nat.pos_of_ne_zero hn) one_pos
  · intro y z h
    rw [eval_eq_sum_range' (Nat.lt_succ_of_le hp), eval_finsetSum, eval_finsetSum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [rot_eval a b m y z h, eval_mul, eval_mul, eval_C]
    ring
end Formalism.FourierDecayAlt.P.Markov
