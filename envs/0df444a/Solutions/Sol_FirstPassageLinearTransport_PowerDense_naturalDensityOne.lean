-- Prove2me | solution 1 for FirstPassageLinearTransport.PowerDense.naturalDensityOne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:58:42.337057+00:00
-- url     : https://prove2.me/submissions/0d24d013-171d-4de7-9afb-05ddd13f993f

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_Density
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_D_pos
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_bad_bound
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
namespace PowerDense
theorem _root_.solution {S : Set ℕ} {C D : ℝ}
    (h : PowerDense S C D) : NaturalDensityOne S := by
  have hpow : Filter.Tendsto (fun X : ℕ => (X : ℝ) ^ (-D))
      Filter.atTop (nhds 0) := by
    exact (tendsto_rpow_neg_atTop h.D_pos).comp
      tendsto_natCast_atTop_atTop
  have hupper : ∀ᶠ X : ℕ in Filter.atTop,
      (badCount S X : ℝ) / X ≤ C * (X : ℝ) ^ (-D) := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with X hX
    have hXR : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
    have hbad := h.bad_bound X hX
    calc
      (badCount S X : ℝ) / X ≤
          (C * (X : ℝ) ^ (1 - D)) / X :=
        div_le_div_of_nonneg_right hbad hXR.le
      _ = C * (X : ℝ) ^ (-D) := by
        rw [show (1 : ℝ) - D = 1 + (-D) by ring,
          Real.rpow_add hXR, Real.rpow_one]
        field_simp
  have hnonneg : ∀ X : ℕ, 0 ≤ (badCount S X : ℝ) / X := by
    intro X
    positivity
  unfold NaturalDensityOne
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds (by
      simpa using (tendsto_const_nhds.mul hpow :
        Filter.Tendsto (fun X : ℕ => C * (X : ℝ) ^ (-D))
          Filter.atTop (nhds (C * 0))))
  · filter_upwards with X
    exact hnonneg X
  · exact hupper
end PowerDense
end FirstPassageLinearTransport
