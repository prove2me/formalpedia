-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.BoxTail.tc_right_pt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:51.959801+00:00
-- url     : https://prove2.me/submissions/5e4ccb87-9355-414c-8531-f7aa721c31d1

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailKernel
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PerronHorizontalSegmentBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailContourB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.BoxTail
namespace Formalism.HermitianLattices.Ext.BoxTail
theorem _root_.solution {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (C₀ : ℝ)
    (hR : ∀ s : ℂ, 1 < s.re → ‖Formalism.ZeroFreeDirichlet.negLD χ s‖ ≤ 1 / (s.re - 1) + C₀)
    (y t : ℝ) (hy : 0 < y) (ht : t ≠ 0) :
    ‖Formalism.ZeroFreeDirichlet.Fchi χ y (((2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ (1 + C₀) * y ^ 2 / t ^ 2 := by
  set s : ℂ := ((2 : ℝ) : ℂ) + (t : ℂ) * I with hs
  have hre : s.re = 2 := by simp [hs]
  have him : s.im = t := by simp [hs]
  have hN : ‖Formalism.ZeroFreeDirichlet.negLD χ s‖ ≤ 1 + C₀ := by
    have h0 := hR s (by rw [hre]; norm_num)
    rw [hre] at h0
    norm_num at h0
    linarith
  have hY : ‖(y : ℂ) ^ s‖ = y ^ 2 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hy, hre, Real.rpow_two]
  have h1 : |t| ≤ ‖s‖ := by rw [← him]; exact Complex.abs_im_le_norm s
  have h2 : |t| ≤ ‖s - 1‖ := by
    have e : (s - 1).im = t := by simp [him]
    rw [← e]; exact Complex.abs_im_le_norm _
  have ht2 : 0 < t ^ 2 := by positivity
  have hD : t ^ 2 ≤ ‖s * (s - 1)‖ := by
    rw [norm_mul, ← sq_abs, sq]
    exact mul_le_mul h1 h2 (abs_nonneg t) (norm_nonneg _)
  unfold Formalism.ZeroFreeDirichlet.Fchi
  rw [norm_div, norm_mul, hY]
  calc ‖Formalism.ZeroFreeDirichlet.negLD χ s‖ * y ^ 2 / ‖s * (s - 1)‖ ≤ (1 + C₀) * y ^ 2 / ‖s * (s - 1)‖ := by
        gcongr
    _ ≤ (1 + C₀) * y ^ 2 / t ^ 2 := by
        have hC : 0 ≤ 1 + C₀ := le_trans (norm_nonneg _) hN
        exact div_le_div_of_nonneg_left (by positivity) ht2 hD
end Formalism.HermitianLattices.Ext.BoxTail
