-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Markov.abs_eval_le_of_nodes
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:42.463632+00:00
-- url     : https://prove2.me/submissions/7fe8794d-2e76-4cdd-bdf5-7b73f2a37e31

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
theorem _root_.solution (s : Finset ℕ) (v : ℕ → ℝ) (hvs : Set.InjOn v s) (r : ℝ[X])
    (hr : r.degree < #s) (K : ℝ)
    (hK : ∀ i ∈ s, |r.eval (v i)| ≤ K * |(derivative (Lagrange.nodal s v)).eval (v i)|)
    (y : ℝ) (hy : ∀ i ∈ s, v i < y) :
    |r.eval y| ≤ K * (derivative (Lagrange.nodal s v)).eval y := by
  have hne : ∀ i ∈ s, y ≠ v i := fun i hi => (hy i hi).ne'
  have hNpos : 0 < (Lagrange.nodal s v).eval y := by
    rw [Lagrange.eval_nodal]; exact Finset.prod_pos fun i hi => sub_pos.mpr (hy i hi)
  have hd : (derivative (Lagrange.nodal s v)).degree < #s := by
    have := degree_derivative_lt (Lagrange.nodal_ne_zero (s := s) (v := v))
    rwa [Lagrange.degree_nodal] at this
  have e1 : r.eval y = (Lagrange.nodal s v).eval y *
      ∑ i ∈ s, Lagrange.nodalWeight s v i * (y - v i)⁻¹ * r.eval (v i) := by
    conv_lhs => rw [Lagrange.eq_interpolate hvs hr]
    exact Lagrange.eval_interpolate_not_at_node _ hne
  have e2 : (derivative (Lagrange.nodal s v)).eval y = (Lagrange.nodal s v).eval y *
      ∑ i ∈ s, Lagrange.nodalWeight s v i * (y - v i)⁻¹ *
        (derivative (Lagrange.nodal s v)).eval (v i) := by
    conv_lhs => rw [Lagrange.eq_interpolate hvs hd]
    exact Lagrange.eval_interpolate_not_at_node _ hne
  have hw : ∀ i ∈ s, Lagrange.nodalWeight s v i *
      (derivative (Lagrange.nodal s v)).eval (v i) = 1 := by
    intro i hi
    have h0 := Lagrange.nodalWeight_ne_zero hvs hi
    rw [Lagrange.nodalWeight_eq_eval_derivative_nodal hi] at h0 ⊢
    exact inv_mul_cancel₀ (by simpa using h0)
  rw [e1, e2, abs_mul, abs_of_pos hNpos, mul_left_comm]
  refine mul_le_mul_of_nonneg_left ?_ hNpos.le
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  have hpos : 0 < (y - v i)⁻¹ := inv_pos.mpr (sub_pos.mpr (hy i hi))
  have h1 := hw i hi
  have h2 : |Lagrange.nodalWeight s v i| *
      |(derivative (Lagrange.nodal s v)).eval (v i)| = 1 := by
    rw [← abs_mul, h1, abs_one]
  rw [abs_mul, abs_mul, abs_of_pos hpos]
  calc |Lagrange.nodalWeight s v i| * (y - v i)⁻¹ * |r.eval (v i)|
      ≤ |Lagrange.nodalWeight s v i| * (y - v i)⁻¹ *
        (K * |(derivative (Lagrange.nodal s v)).eval (v i)|) := by
        exact mul_le_mul_of_nonneg_left (hK i hi) (mul_nonneg (abs_nonneg _) hpos.le)
    _ = K * (y - v i)⁻¹ * (|Lagrange.nodalWeight s v i| *
        |(derivative (Lagrange.nodal s v)).eval (v i)|) := by ring
    _ = K * ((y - v i)⁻¹ * (Lagrange.nodalWeight s v i *
        (derivative (Lagrange.nodal s v)).eval (v i))) := by rw [h1, h2]; ring
    _ = _ := by ring
end Formalism.FourierDecayAlt.P.Markov
