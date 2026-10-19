-- Prove2me | solution 1 for CohnElkies.upper_inv_one_sub_exp_neg_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:26.273981+00:00
-- url     : https://prove2.me/submissions/76801558-0d52-47ac-a783-a262e93ffdc4

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {x : ℝ} (hx : 0 < x) :
    x⁻¹ ≤ (1 - Real.exp (-x))⁻¹ ∧
      (1 - Real.exp (-x))⁻¹ ≤ 1 + x⁻¹ := by
  have hden : 0 < 1 - Real.exp (-x) := by
    have he : Real.exp (-x) < 1 :=
      Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hlower : 1 - Real.exp (-x) ≤ x := by
    nlinarith [Real.add_one_le_exp (-x)]
  have hplus : 0 < 1 + x := by
    linarith
  have hexp : Real.exp (-x) ≤ (1 + x)⁻¹ := by
    rw [Real.exp_neg]
    apply (inv_le_inv₀ (Real.exp_pos x) hplus).2
    nlinarith [Real.add_one_le_exp x]
  constructor
  · exact (inv_le_inv₀ hx hden).2 hlower
  · have hgoal :
        1 / (1 - Real.exp (-x)) ≤ 1 + x⁻¹ := by
      apply (div_le_iff₀ hden).2
      have hfactor : 0 ≤ 1 + x⁻¹ := by
        positivity
      calc
        (1 : ℝ) =
            (1 + x⁻¹) * (1 - (1 + x)⁻¹) := by
              field_simp [hx.ne', hplus.ne']; ring
        _ ≤ (1 + x⁻¹) * (1 - Real.exp (-x)) :=
          mul_le_mul_of_nonneg_left
            (sub_le_sub_left hexp 1) hfactor
    simpa [one_div] using! hgoal
end CohnElkies
