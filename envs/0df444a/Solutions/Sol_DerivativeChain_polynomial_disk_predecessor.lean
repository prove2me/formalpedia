-- Prove2me | solution 1 for DerivativeChain.polynomial_disk_predecessor
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-17T18:46:43.369045+00:00
-- url     : https://prove2.me/submissions/5b9e6616-3d8f-484e-9504-f0636add1493

import Theorems.Thm_DerivativeChain_exists_root_transition
import Theorems.Thm_DerivativeChainPrivate_complex_close_predecessor
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.GaussLucas
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
open scoped BigOperators Polynomial
set_option autoImplicit false
theorem solution {P : ℂ[X]} {z : ℂ}
    (hP : 0 < P.degree) (hz : P.derivative.eval z = 0)
    (hdisk : ∀ w : ℂ, P.eval w = 0 → ‖w‖ ≤ 1) :
    ∃ w : ℂ, P.eval w = 0 ∧ ‖w - z‖ ^ 2 ≤ 1 - ‖z‖ ^ 2 := by
  classical
  obtain ⟨π, hπ, hsum, hmean_re, hmean_im, hroot⟩ :=
    DerivativeChain.exists_root_transition hP hz
  have hs : (Finset.univ : Finset P.roots.toFinset).Nonempty := by
    exact Finset.nonempty_of_sum_ne_zero
      (show (∑ w, π w) ≠ 0 by rw [hsum]; exact one_ne_zero)
  obtain ⟨w, _, hw⟩ := DerivativeChainPrivate.complex_close_predecessor
    Finset.univ hs π (fun w : P.roots.toFinset => (w : ℂ)) z
    (fun w _ => hπ w) hsum hmean_re.symm hmean_im.symm
    (fun w _ => hdisk w (hroot w))
  exact ⟨w, hroot w, hw⟩
