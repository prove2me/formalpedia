-- Prove2me | solution 1 for CohnElkies.upperGammaVarianceDensity_pointwise_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:26.273981+00:00
-- url     : https://prove2.me/submissions/048b8f5f-dbeb-4e5f-b608-90b46b71550a

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upper_inv_one_sub_exp_neg_bounds

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
    {ℓ η a : ℝ} (hℓ : 0 < ℓ) (ha : 0 < a) :
    (ℓ / 2) * Real.exp (-η * a) ≤
      a ^ 2 * upperGammaMeasureDensity ℓ η a ∧
    a ^ 2 * upperGammaMeasureDensity ℓ η a ≤
      (a + ℓ / 2) * Real.exp (-η * a) := by
  let x : ℝ := 2 * a / ℓ
  have hx : 0 < x := by
    try dsimp [x]
    positivity
  have hkernel := upper_inv_one_sub_exp_neg_bounds hx
  have hden : 0 < 1 - Real.exp (-x) := by
    have he : Real.exp (-x) < 1 :=
      Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hfactor : 0 ≤ a * Real.exp (-η * a) := by
    positivity
  have hidentity :
      a ^ 2 * upperGammaMeasureDensity ℓ η a =
        a * Real.exp (-η * a) *
          (1 - Real.exp (-x))⁻¹ := by
    unfold upperGammaMeasureDensity
    try dsimp [x]
    field_simp [ha.ne', hℓ.ne', hden.ne']
  constructor
  · calc
      (ℓ / 2) * Real.exp (-η * a) =
          a * Real.exp (-η * a) * x⁻¹ := by
            try dsimp [x]
            field_simp [ha.ne', hℓ.ne']
      _ ≤ a * Real.exp (-η * a) *
          (1 - Real.exp (-x))⁻¹ :=
        mul_le_mul_of_nonneg_left hkernel.1 hfactor
      _ = a ^ 2 * upperGammaMeasureDensity ℓ η a :=
        hidentity.symm
  · calc
      a ^ 2 * upperGammaMeasureDensity ℓ η a =
          a * Real.exp (-η * a) *
            (1 - Real.exp (-x))⁻¹ := hidentity
      _ ≤ a * Real.exp (-η * a) * (1 + x⁻¹) :=
        mul_le_mul_of_nonneg_left hkernel.2 hfactor
      _ = (a + ℓ / 2) * Real.exp (-η * a) := by
        try dsimp [x]
        field_simp [ha.ne', hℓ.ne']
end CohnElkies
