-- Prove2me | solution 1 for CohnElkies.integral_profileNegativePart_eq_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:22.892104+00:00
-- url     : https://prove2.me/submissions/0c4785e1-0a92-4e1e-bcab-500f30e744a9

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_abs_sub_eq_two_profileNegativePart

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution {φ : ℝ → ℝ}
    (hφ : Integrable φ)
    (hmean : (∫ v : ℝ, φ v) = 0)
    (hmass : (∫ v : ℝ, |φ v|) = 1) :
    (∫ v : ℝ, profileNegativePart φ v) = (1 / 2 : ℝ) := by
  have hsigned : (∫ v : ℝ, (|φ v| - φ v)) = 1 := by
    rw [integral_sub hφ.abs hφ, hmass, hmean]
    norm_num
  have htwice :
      (∫ v : ℝ, (|φ v| - φ v)) =
        2 * ∫ v : ℝ, profileNegativePart φ v := by
    calc
      (∫ v : ℝ, (|φ v| - φ v)) =
          ∫ v : ℝ, 2 * profileNegativePart φ v := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall
          (abs_sub_eq_two_profileNegativePart φ)
      _ = 2 * ∫ v : ℝ, profileNegativePart φ v := by
        rw [integral_const_mul]
  linarith
end CohnElkies
