-- Prove2me | solution 1 for Formalism.ZRN.riemannZetaOne_eq_one_sub_of_re_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:47:13.901602+00:00
-- url     : https://prove2.me/submissions/9f1d7e43-4649-4246-8ea9-de31f00b5b90

import Definitions.Def_Formalism_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaRealNonvanish
import Theorems.Thm_Formalism_ZRN_F_differentiableAt
import Theorems.Thm_Formalism_ZRN_F_eq

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
open Formalism.ZRN
namespace Formalism.ZRN
theorem _root_.solution (s : ℂ) (h : 0 < s.re) : riemannZeta₁ s = 1 - F s := by
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const continuous_re
  have hF : AnalyticOnNhd ℂ (fun s => 1 - F s) {s : ℂ | 0 < s.re} := by
    rw [Complex.analyticOnNhd_iff_differentiableOn hU]
    intro z hz
    exact ((F_differentiableAt z hz).const_sub 1).differentiableWithinAt
  have hZ : AnalyticOnNhd ℂ riemannZeta₁ {s : ℂ | 0 < s.re} :=
    fun z _ => differentiable_riemannZeta₁.analyticAt z
  have hpc : IsPreconnected {s : ℂ | 0 < s.re} := (convex_halfSpace_re_gt 0).isPreconnected
  have h2 : (2 : ℂ) ∈ {s : ℂ | 0 < s.re} := by simp
  have hev : riemannZeta₁ =ᶠ[𝓝 (2 : ℂ)] (fun s => 1 - F s) := by
    have ho : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num)
    filter_upwards [ho] with s hs
    have hs1 : s ≠ 1 := by rintro rfl; simp at hs
    rw [F_eq s hs, riemannZeta_eq_inv_sub_mul hs1]
    have hne : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    field_simp
    ring
  exact hZ.eqOn_of_preconnected_of_eventuallyEq hF hpc h2 hev h
end Formalism.ZRN
