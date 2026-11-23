-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Markov.schur
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:29:35.504901+00:00
-- url     : https://prove2.me/submissions/3b43f224-d3e4-449b-9036-a6c11b1c7656

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Markov
import Theorems.Thm_Formalism_FourierDecayAlt_P_Markov_abs_eval_le_of_nodes
import Theorems.Thm_Formalism_FourierDecayAlt_P_Markov_injOn_cos_th
import Theorems.Thm_Formalism_FourierDecayAlt_P_Markov_T_eq_nodal
import Theorems.Thm_Formalism_FourierDecayAlt_P_Markov_abs_U_mul_sin

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
theorem _root_.solution (n : ℕ) (hn : n ≠ 0) (r : ℝ[X]) (hr : r.degree < n) (c : ℝ)
    (hC : ∀ k < n, |sin (th n k) * r.eval (cos (th n k))| ≤ c)
    (y : ℝ) (hy : ∀ k < n, cos (th n k) < y) (hy1 : y ≤ 1) : |r.eval y| ≤ n * c := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hc : 0 ≤ c := (abs_nonneg _).trans (hC 0 hn0)
  have hym : -1 ≤ y := (neg_one_le_cos _).trans (hy 0 hn0).le
  have hT' : derivative (Chebyshev.T ℝ n) = C ((2 : ℝ) ^ (n - 1)) *
      derivative (Lagrange.nodal (Finset.range n) (fun k => cos (th n k))) := by
    conv_lhs => rw [T_eq_nodal n hn, derivative_C_mul]
  have hTe : ∀ x : ℝ, (derivative (Chebyshev.T ℝ n)).eval x = (2 : ℝ) ^ (n - 1) *
      (derivative (Lagrange.nodal (Finset.range n) (fun k => cos (th n k)))).eval x := by
    intro x; rw [hT']; simp
  have hUe : ∀ x : ℝ, (derivative (Chebyshev.T ℝ n)).eval x =
      n * (Chebyshev.U ℝ ((n : ℤ) - 1)).eval x := by
    intro x; rw [Chebyshev.T_derivative_eq_U]; simp
  have key := abs_eval_le_of_nodes (Finset.range n) (fun k => cos (th n k)) (injOn_cos_th n) r
    (by simpa using hr) (c / n * 2 ^ (n - 1)) ?_ y (by simpa using hy)
  · have h2 : (derivative (Chebyshev.T ℝ n)).eval y ≤ (n : ℝ) ^ 2 := by
      have h3 := Chebyshev.abs_iterate_derivative_T_real_le n 1 (x := y) (abs_le.mpr ⟨hym, hy1⟩)
      simp only [Function.iterate_one, Chebyshev.derivative_T_eval_one] at h3
      exact (le_abs_self _).trans (by simpa using h3)
    calc |r.eval y| ≤ c / n * ((2 : ℝ) ^ (n - 1) *
          (derivative (Lagrange.nodal (Finset.range n) (fun k => cos (th n k)))).eval y) := by
          rw [← mul_assoc]; exact key
      _ = c / n * (derivative (Chebyshev.T ℝ n)).eval y := by rw [hTe]
      _ ≤ c / n * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = n * c := by field_simp
  · intro k hk
    have hk' : k < n := Finset.mem_range.mp hk
    have h1 := abs_U_mul_sin n k hn
    have h2 := hC k hk'
    rw [abs_mul] at h2
    have h3 : c / n * 2 ^ (n - 1) *
        |(derivative (Lagrange.nodal (Finset.range n) (fun k => cos (th n k)))).eval
          (cos (th n k))| = c * |(Chebyshev.U ℝ ((n : ℤ) - 1)).eval (cos (th n k))| := by
      have h4 := (hTe (cos (th n k))).symm.trans (hUe (cos (th n k)))
      have h5 := congrArg abs h4
      rw [abs_mul, abs_mul, abs_of_pos hn', abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (n - 1))] at h5
      rw [mul_assoc, h5]; field_simp
    show |r.eval (cos (th n k))| ≤ _
    rw [h3]
    calc |r.eval (cos (th n k))|
        = (|sin (th n k)| * |r.eval (cos (th n k))|) *
          |(Chebyshev.U ℝ ((n : ℤ) - 1)).eval (cos (th n k))| := by
          rw [mul_right_comm, mul_comm |sin (th n k)|, h1, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
end Formalism.FourierDecayAlt.P.Markov
