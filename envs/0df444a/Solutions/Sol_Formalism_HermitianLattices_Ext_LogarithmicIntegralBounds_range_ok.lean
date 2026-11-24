-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.range_ok
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:39:45.957608+00:00
-- url     : https://prove2.me/submissions/f5f66468-5f75-4b43-87e0-6c2266379bfc

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
theorem _root_.solution {C₀ ε x Λ Y : ℝ} (hε : 0 < ε) (hx : 1 ≤ x) (hΛ : 1 ≤ Λ) (hl1 : 1 ≤ Real.log x)
    (hl : 4 * |C₀| * (5 + ε / 5) ≤ Real.log x)
    (h1 : (1 / 4) * Real.log x ^ 2 * Λ ≤ Y) (h3 : Y ≤ x ^ (ε / 5) * Real.log x ^ 2) :
    C₀ * Λ * Real.log (Λ + 2) ≤ Y := by
  set L := Real.log x with hLdef
  have hL0 : 0 < L := by linarith
  have hxpos : 0 < x := by linarith
  have hxr : 0 < x ^ (ε / 5) := Real.rpow_pos_of_pos hxpos _
  have hxe1 : 1 ≤ x ^ (ε / 5) := Real.one_le_rpow hx (by linarith)
  have hΛle : Λ ≤ 4 * x ^ (ε / 5) := by
    have h13 : (1 / 4) * L ^ 2 * Λ ≤ x ^ (ε / 5) * L ^ 2 := le_trans h1 h3
    have hL2 : 0 < L ^ 2 := pow_pos hL0 2
    nlinarith
  have hlogΛ : Real.log (Λ + 2) ≤ Real.log 6 + ε / 5 * L := by
    have h6 : Λ + 2 ≤ 6 * x ^ (ε / 5) := by linarith
    have h := Real.log_le_log (by linarith) h6
    rw [Real.log_mul (by norm_num) hxr.ne', Real.log_rpow hxpos] at h
    exact h
  have hlog6 : Real.log 6 ≤ 5 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 6)
    linarith
  have hlogpos : 0 ≤ Real.log (Λ + 2) := Real.log_nonneg (by linarith)
  have hkey : |C₀| * Real.log (Λ + 2) ≤ L ^ 2 / 4 := by
    have hA0 := abs_nonneg C₀
    have hb : Real.log (Λ + 2) ≤ L * (5 + ε / 5) := by nlinarith
    have h1' : |C₀| * Real.log (Λ + 2) ≤ |C₀| * (L * (5 + ε / 5)) := mul_le_mul_of_nonneg_left hb hA0
    have h2' : (4 * |C₀| * (5 + ε / 5)) * L ≤ L * L := mul_le_mul_of_nonneg_right hl hL0.le
    nlinarith
  have hΛlog : 0 ≤ Λ * Real.log (Λ + 2) := mul_nonneg (by linarith) hlogpos
  calc C₀ * Λ * Real.log (Λ + 2) = C₀ * (Λ * Real.log (Λ + 2)) := by ring
    _ ≤ |C₀| * (Λ * Real.log (Λ + 2)) := mul_le_mul_of_nonneg_right (le_abs_self C₀) hΛlog
    _ = Λ * (|C₀| * Real.log (Λ + 2)) := by ring
    _ ≤ Λ * (L ^ 2 / 4) := mul_le_mul_of_nonneg_left hkey (by linarith)
    _ = (1 / 4) * L ^ 2 * Λ := by ring
    _ ≤ Y := h1
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
