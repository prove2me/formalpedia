-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Markov.rot_natDegree
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:41.38253+00:00
-- url     : https://prove2.me/submissions/e80da200-1628-49fa-b973-01353dac8c8e

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Markov

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
theorem _root_.solution (a b : ℝ) (m : ℕ) :
    (rot a b m).1.natDegree ≤ m ∧ (rot a b (m + 1)).2.natDegree ≤ m ∧
      ((1 - X ^ 2) * (rot a b m).2).natDegree ≤ m + 1 := by
  induction m with
  | zero => simp [rot]
  | succ m ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    have hA : (rot a b (m + 1)).1.natDegree ≤ m + 1 := by
      show (C a * X * (rot a b m).1 + C b * ((1 - X ^ 2) * (rot a b m).2)).natDegree ≤ m + 1
      refine natDegree_add_le_of_degree_le ?_ ((natDegree_C_mul_le _ _).trans h3)
      rw [mul_assoc]
      refine (natDegree_C_mul_le _ _).trans ?_
      refine natDegree_mul_le.trans ?_
      rw [natDegree_X]; omega
    refine ⟨hA, ?_, ?_⟩
    · show (C b * (rot a b (m + 1)).1 + C a * X * (rot a b (m + 1)).2).natDegree ≤ m + 1
      refine natDegree_add_le_of_degree_le ((natDegree_C_mul_le _ _).trans hA) ?_
      rw [mul_assoc]
      refine (natDegree_C_mul_le _ _).trans ?_
      refine natDegree_mul_le.trans ?_
      rw [natDegree_X]; omega
    · refine natDegree_mul_le.trans ?_
      have : ((1 : ℝ[X]) - X ^ 2).natDegree ≤ 2 := by compute_degree
      omega
end Formalism.FourierDecayAlt.P.Markov
