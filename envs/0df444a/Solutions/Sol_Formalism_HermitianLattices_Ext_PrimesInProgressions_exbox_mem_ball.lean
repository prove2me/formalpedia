-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.exbox_mem_ball
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:19:55.199942+00:00
-- url     : https://prove2.me/submissions/5c620070-4e02-4c80-a48b-b77182f184f3

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplLocL
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplBox
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exLF_re_lt_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.ZeroFreeDirichlet
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) {ρ : ℂ} {u : ℝ}
    (h0 : exLF χ ρ = 0) (h1 : 9 / 10 ≤ ρ.re) (h2 : |ρ.im - u| ≤ 1 / 14) :
    ρ ∈ Metric.closedBall ((101 / 100 : ℂ) + u * I) (2 / 15) := by
  have h3 := exLF_re_lt_one χ h0
  have e : (101 / 100 : ℂ) = ((101 / 100 : ℝ) : ℂ) := by push_cast; rfl
  rw [Metric.mem_closedBall, dist_eq_norm]
  have h4 : ‖ρ - ((101 / 100 : ℂ) + u * I)‖ ^ 2 ≤ (2 / 15 : ℝ) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, e]
    simp only [sub_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, sub_im, add_im, mul_im, zero_add]
    obtain ⟨h5, h6⟩ := abs_le.1 h2
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by norm_num) (by norm_num)).1 h4
end Formalism.HermitianLattices.Ext.PrimesInProgressions
