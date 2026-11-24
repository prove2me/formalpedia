-- Prove2me | solution 1 for Formalism.HF.P.summable_log_div_rpow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:02.33329+00:00
-- url     : https://prove2.me/submissions/9c7cf6a1-0854-461c-8788-883170062a99

import Mathlib
import Definitions.Def_Formalism_DirichletDensity_Statement
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_LogToDir
import Theorems.Thm_Formalism_HF_P_log_div_rpow_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Set
noncomputable section
open Formalism Formalism.HF Formalism.HF.P
namespace Formalism.HF.P
theorem _root_.solution {y : ℝ} (hy : 1 < y) :
    Summable (fun n : ℕ => Real.log n / (n : ℝ) ^ y) := by
  set ε := (y - 1) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hs : Summable (fun n : ℕ => (1 / ε) * ((n : ℝ) ^ (y - ε))⁻¹) :=
    (Real.summable_nat_rpow_inv.2 (by rw [hε]; linarith)).mul_left _
  refine Summable.of_nonneg_of_le (fun n => log_div_rpow_nonneg n y) (fun n => ?_) hs
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, Real.log_zero, zero_div]
    exact mul_nonneg (div_nonneg zero_le_one hε0.le) (inv_nonneg.2 (Real.rpow_nonneg le_rfl _))
  · have hn' : (0:ℝ) < n := Nat.cast_pos.2 hn
    have h1 := Real.log_le_rpow_div hn'.le hε0
    have hpos : 0 < (n:ℝ) ^ y := Real.rpow_pos_of_pos hn' y
    have hposε : 0 < (n:ℝ) ^ ε := Real.rpow_pos_of_pos hn' ε
    calc Real.log n / (n:ℝ) ^ y ≤ ((n:ℝ) ^ ε / ε) / (n:ℝ) ^ y := by gcongr
      _ = (1 / ε) * ((n:ℝ) ^ (y - ε))⁻¹ := by
        rw [Real.rpow_sub hn', inv_div]
        field_simp
end Formalism.HF.P
