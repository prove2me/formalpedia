-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Markov.T_eq_nodal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:42.254395+00:00
-- url     : https://prove2.me/submissions/cc24eacf-ef82-454c-8b2e-40b1261dd676

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Markov
import Theorems.Thm_Formalism_FourierDecayAlt_P_Markov_injOn_cos_th

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
theorem _root_.solution (n : ℕ) (hn : n ≠ 0) :
    Chebyshev.T ℝ n =
      C ((2 : ℝ) ^ (n - 1)) * Lagrange.nodal (Finset.range n) (fun k => cos (th n k)) := by
  have h2 : ((2 : ℝ) ^ (n - 1)) ≠ 0 := by positivity
  apply eq_of_degree_le_of_eval_index_eq (Finset.range n) (injOn_cos_th n)
  · simp
  · rw [degree_C_mul h2, Lagrange.degree_nodal]; simp
  · rw [leadingCoeff_mul, leadingCoeff_C, Lagrange.nodal_monic.leadingCoeff]; simp
  · intro i hi
    have h0 : eval (cos (th n i)) (Lagrange.nodal (Finset.range n) fun k => cos (th n k)) = 0 :=
      Lagrange.eval_nodal_at_node (v := fun k => cos (th n k)) hi
    rw [eval_mul, h0, mul_zero, Chebyshev.T_real_cos, cos_eq_zero_iff]
    refine ⟨i, ?_⟩
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    simp only [th]
    push_cast
    field_simp
end Formalism.FourierDecayAlt.P.Markov
