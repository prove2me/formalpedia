-- Prove2me | solution 1 for Formalism.ZF.zeroFreeBoundedHeight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:43:11.240832+00:00
-- url     : https://prove2.me/submissions/180e5990-8461-4a4d-9bbf-e20205a7cbcb

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_SmallHeight

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
theorem _root_.solution : SmallHeight := by
  unfold SmallHeight
  intro T
  have hopen : IsOpen {s : ℂ | s ≠ 1 → riemannZeta s ≠ 0} := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    by_cases hz1 : z = 1
    · subst hz1
      have h := riemannZeta_residue_one.eventually_ne one_ne_zero
      rw [eventually_nhdsWithin_iff] at h
      filter_upwards [h] with x hx hx1
      exact right_ne_zero_of_mul (hx hx1)
    · have hc : ContinuousAt riemannZeta z := (differentiableAt_riemannZeta hz1).continuousAt
      filter_upwards [hc.eventually_ne (hz hz1)] with x hx _
      exact hx
  set K : Set ℂ := (fun y : ℝ => (1 : ℂ) + (y : ℂ) * I) '' Icc (-T) T
  have hKc : IsCompact K :=
    isCompact_Icc.image (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
  have hKsub : K ⊆ {s : ℂ | s ≠ 1 → riemannZeta s ≠ 0} := by
    rintro _ ⟨y, -, rfl⟩ _
    apply riemannZeta_ne_zero_of_one_le_re
    simp
  obtain ⟨δ, hδ, hsub⟩ := hKc.exists_cthickening_subset_open hopen hKsub
  refine ⟨δ, hδ, fun s hs hre hs1 => ?_⟩
  by_cases hle : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re hle
  · push_neg at hle
    have hp : (1 : ℂ) + (s.im : ℂ) * I ∈ K := ⟨s.im, abs_le.mp hs, rfl⟩
    have hre1 : ((1 : ℂ) + (s.im : ℂ) * I).re = 1 := by simp
    have him1 : s.im = ((1 : ℂ) + (s.im : ℂ) * I).im := by simp
    have hd : dist s ((1 : ℂ) + (s.im : ℂ) * I) ≤ δ := by
      rw [Complex.dist_of_im_eq him1, Real.dist_eq, hre1, abs_le]
      constructor <;> linarith
    exact hsub (Metric.mem_cthickening_of_dist_le _ _ _ _ hp hd) hs1
end Formalism.ZF
