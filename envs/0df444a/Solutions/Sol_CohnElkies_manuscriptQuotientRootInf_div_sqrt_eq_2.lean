-- Prove2me | solution 2 for CohnElkies.manuscriptQuotientRootInf_div_sqrt_eq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:01:56.682699+00:00
-- url     : https://prove2.me/submissions/489a8ebd-059a-4237-b15b-6d289ea1aee0

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Topology
open scoped Pointwise in
theorem h47_sInf_mul_image (s : Set ℝ) {c : ℝ} (hc : 0 ≤ c) :
    sInf ((fun t => c * t) '' s) = c * sInf s := by
  rw [show (fun t : ℝ => c * t) = (fun t : ℝ => c • t) from rfl, Set.image_smul,
    Real.sInf_smul_of_nonneg hc, smul_eq_mul]

theorem solution (d : ℕ) :
    sInf (manuscriptQuotientRootSet d) / Real.sqrt (d : ℝ) =
      normalizedProgram d := by
  unfold normalizedProgram manuscriptQuotientRootSet
  have h : Set.range (normalizedCost (d := d)) =
      (fun t => (Real.sqrt (d : ℝ))⁻¹ * t) ''
        Set.range (fun f : Admissible d => quotient f ^ ((d : ℝ)⁻¹)) := by
    rw [← Set.range_comp]
    congr 1
    funext f
    simp only [Function.comp_apply, normalizedCost, div_eq_inv_mul]
  rw [h, h47_sInf_mul_image _ (inv_nonneg.2 (Real.sqrt_nonneg _)), div_eq_inv_mul]

