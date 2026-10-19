-- Prove2me | solution 1 for CohnElkies.upperGammaVarianceDensity_laplace_linear_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.968836+00:00
-- url     : https://prove2.me/submissions/9346e275-c75c-4cdc-ae97-b5351be47b47

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {ℓ η a : ℝ} (hℓ : 0 < ℓ) (ha : 0 < a) :
    a * Real.exp (-η * a) ≤
      a ^ 2 * upperGammaMeasureDensity ℓ η a := by
  let x : ℝ := 2 * a / ℓ
  have hx : 0 < x := by
    try dsimp [x]
    positivity
  have hden : 0 < 1 - Real.exp (-x) := by
    have h := Real.exp_lt_one_iff.mpr
      (show -x < 0 by linarith)
    linarith
  have hdenone : 1 - Real.exp (-x) ≤ 1 := by
    linarith [Real.exp_pos (-x)]
  have hinv : 1 ≤ (1 - Real.exp (-x))⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hden).2
    simpa using! hdenone
  have hfactor : 0 ≤ a * Real.exp (-η * a) := by
    positivity
  calc
    a * Real.exp (-η * a) =
        (a * Real.exp (-η * a)) * 1 := by ring
    _ ≤ (a * Real.exp (-η * a)) *
        (1 - Real.exp (-x))⁻¹ :=
      mul_le_mul_of_nonneg_left hinv hfactor
    _ = a ^ 2 * upperGammaMeasureDensity ℓ η a := by
      unfold upperGammaMeasureDensity
      try dsimp [x]
      field_simp [ha.ne', hden.ne']
end CohnElkies
