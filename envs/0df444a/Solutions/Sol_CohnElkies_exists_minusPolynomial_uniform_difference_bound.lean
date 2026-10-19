-- Prove2me | solution 1 for CohnElkies.exists_minusPolynomial_uniform_difference_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.968836+00:00
-- url     : https://prove2.me/submissions/2f0aaeba-cdfa-40d1-955d-671e73635cf4

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_minusPolynomial_imaginary_norm_ge_three_beta
import Theorems.Thm_CohnElkies_exists_minusPolynomial_uniform_difference_ratio

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ u : ℝ, 1 + ε / 4 ≤ u → ∀ T : ℝ,
        ‖minusPolynomial ε
            ((T : ℂ) + Complex.I * (u : ℂ)) -
          minusPolynomial ε (Complex.I * (u : ℂ))‖ ≤
          C * (|T| + |T| ^ 3) *
            ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_minusPolynomial_uniform_difference_ratio hε
  refine ⟨C, hC, ?_⟩
  intro u hu T
  have hden : 0 <
      ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ := by
    have hbeta := beta_pos hε
    have hnorm :=
      minusPolynomial_imaginary_norm_ge_three_beta hε hu
    nlinarith
  exact (div_le_iff₀ hden).mp (hbound u hu T)
end CohnElkies
