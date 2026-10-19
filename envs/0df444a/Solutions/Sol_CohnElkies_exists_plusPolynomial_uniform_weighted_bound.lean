-- Prove2me | solution 1 for CohnElkies.exists_plusPolynomial_uniform_weighted_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.968836+00:00
-- url     : https://prove2.me/submissions/d91afb0b-36f2-49db-8306-f4ed50abc148

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_plusPolynomial_imaginary_norm_ge_beta
import Theorems.Thm_CohnElkies_exists_plusPolynomial_uniform_norm_ratio

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
      ∀ u : ℝ, -1 ≤ u → ∀ T : ℝ,
        ‖plusPolynomial ε
          ((T : ℂ) + Complex.I * (u : ℂ))‖ ≤
          C * (1 + |T| ^ 3) *
            ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_plusPolynomial_uniform_norm_ratio hε
  refine ⟨C, hC, ?_⟩
  intro u hu T
  have hden : 0 <
      ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ :=
    (beta_pos hε).trans_le
      (plusPolynomial_imaginary_norm_ge_beta hε hu)
  exact (div_le_iff₀ hden).mp (hbound u hu T)
end CohnElkies
