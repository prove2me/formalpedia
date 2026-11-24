-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.BoxTail.tc_horiz_pt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:51.082431+00:00
-- url     : https://prove2.me/submissions/bf1c461d-6403-4d8e-a748-f3a3815c08c1

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
theorem _root_.solution {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (M y T x v : ℝ) (hy : 1 ≤ y)
    (hT : 0 < T) (hv : |v| = T) (hx2 : x ≤ 2)
    (hM : ‖Formalism.ZeroFreeDirichlet.negLD χ ((x : ℂ) + (v : ℂ) * I)‖ ≤ M) :
    ‖Formalism.ZeroFreeDirichlet.Fchi χ y ((x : ℂ) + (v : ℂ) * I)‖ ≤ M * y ^ 2 / T ^ 2 := by
  set s : ℂ := (x : ℂ) + (v : ℂ) * I with hs
  have hre : s.re = x := by simp [hs]
  have him : s.im = v := by simp [hs]
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) hM
  have hy0 : 0 < y := by linarith
  have hY : ‖(y : ℂ) ^ s‖ ≤ y ^ 2 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hy0, hre, ← Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le hy hx2
  have h1 : T ≤ ‖s‖ := by rw [← hv, ← him]; exact Complex.abs_im_le_norm s
  have h2 : T ≤ ‖s - 1‖ := by
    have e : (s - 1).im = v := by simp [him]
    rw [← hv, ← e]; exact Complex.abs_im_le_norm _
  have hT2 : 0 < T ^ 2 := by positivity
  have hD : T ^ 2 ≤ ‖s * (s - 1)‖ := by
    rw [norm_mul, sq]
    exact mul_le_mul h1 h2 hT.le (norm_nonneg _)
  unfold Formalism.ZeroFreeDirichlet.Fchi
  rw [norm_div, norm_mul]
  calc ‖Formalism.ZeroFreeDirichlet.negLD χ s‖ * ‖(y : ℂ) ^ s‖ / ‖s * (s - 1)‖ ≤ M * y ^ 2 / ‖s * (s - 1)‖ := by
        gcongr
    _ ≤ M * y ^ 2 / T ^ 2 := div_le_div_of_nonneg_left (by positivity) hT2 hD
end Formalism.HermitianLattices.Ext.BoxTail
