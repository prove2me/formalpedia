-- Prove2me | solution 1 for Formalism.zetaRealNonvanish
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:03:35.475651+00:00
-- url     : https://prove2.me/submissions/a90e3e33-8d94-48e8-a19a-7684158c53bf

import Definitions.Def_Formalism_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaRealNonvanish
import Theorems.Thm_Formalism_ZRN_riemannZetaOne_eq_one_sub_of_re_pos
import Theorems.Thm_Formalism_ZRN_e_ofReal
import Theorems.Thm_Formalism_ZRN_tsum_er_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Set Filter Topology
noncomputable section
open Formalism
open ZRN
namespace Formalism
theorem _root_.solution : ZetaRealNonvanish := by
  intro σ h0 h1
  have hσ1 : (σ : ℂ) ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  rw [riemannZeta_eq_inv_sub_mul hσ1]
  refine mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr hσ1)) ?_
  rw [riemannZetaOne_eq_one_sub_of_re_pos _ (by simpa using h0), F]
  simp_rw [e_ofReal]
  rw [← Complex.ofReal_tsum]
  have := tsum_er_le σ h0 h1
  intro h
  have h' := congrArg Complex.re h
  simp at h'
  linarith
end Formalism
