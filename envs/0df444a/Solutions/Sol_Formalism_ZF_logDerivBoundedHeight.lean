-- Prove2me | solution 1 for Formalism.ZF.logDerivBoundedHeight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:58:28.385805+00:00
-- url     : https://prove2.me/submissions/68660d52-afe6-40f4-b786-a03b76a4b0c1

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_SmallHeightLogDeriv
import Theorems.Thm_Formalism_ZF_shld_identity
import Theorems.Thm_P2M_Formalism_ZF_riemannZeta__ne_zero_of_one_le_re_841fbb3d4634

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
open Formalism Formalism.ZF
namespace Formalism.ZF
theorem _root_.solution : SmallHeightLogDeriv := by
  intro T
  have hK : IsCompact (Icc (1 : ℝ) 3 ×ℂ Icc (-T) T) := isCompact_Icc.reProdIm isCompact_Icc
  have hU : IsOpen {s : ℂ | riemannZeta₁ s ≠ 0} :=
    isOpen_ne_fun differentiable_riemannZeta₁.continuous continuous_const
  have hKU : Icc (1 : ℝ) 3 ×ℂ Icc (-T) T ⊆ {s : ℂ | riemannZeta₁ s ≠ 0} := fun s hs =>
    riemannZeta₁_ne_zero_of_one_le_re (Complex.mem_reProdIm.mp hs).1.1
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_thickening_subset_open hU hKU
  have hne : ∀ s : ℂ, |s.im| ≤ T → 1 - δ / 2 ≤ s.re → s.re ≤ 3 → riemannZeta₁ s ≠ 0 := by
    intro s him hre hre3
    by_cases h1 : 1 ≤ s.re
    · exact riemannZeta₁_ne_zero_of_one_le_re h1
    · apply hδU
      rw [Metric.mem_thickening_iff]
      refine ⟨1 + s.im * I, ?_, ?_⟩
      · rw [Complex.mem_reProdIm]
        obtain ⟨h3, h4⟩ := abs_le.mp him
        refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp <;> linarith
      · rw [Complex.dist_eq]
        have hd : s - (1 + s.im * I) = ((s.re - 1 : ℝ) : ℂ) := by
          apply Complex.ext <;> simp
        rw [hd, Complex.norm_real, Real.norm_eq_abs, abs_lt]
        constructor <;> linarith
  refine ⟨δ / 2, ?_⟩
  have hKc : IsCompact (Icc (1 - δ / 2) 3 ×ℂ Icc (-T) T) := isCompact_Icc.reProdIm isCompact_Icc
  have hcont : ContinuousOn (fun s => deriv riemannZeta₁ s / riemannZeta₁ s)
      (Icc (1 - δ / 2) 3 ×ℂ Icc (-T) T) := by
    apply ContinuousOn.div
    · exact ((differentiable_riemannZeta₁.differentiableOn.deriv isOpen_univ).continuousOn).mono
        (subset_univ _)
    · exact differentiable_riemannZeta₁.continuous.continuousOn
    · intro s hs
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := Complex.mem_reProdIm.mp hs
      exact hne s (abs_le.mpr ⟨h3, h4⟩) h1 h2
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hcont
  refine ⟨C, half_pos hδ, ?_⟩
  intro s hs him hre hre3
  rw [shld_identity hs (hne s him hre hre3)]
  exact hC s (Complex.mem_reProdIm.mpr ⟨⟨hre, hre3⟩, abs_le.mp him⟩)
end Formalism.ZF
