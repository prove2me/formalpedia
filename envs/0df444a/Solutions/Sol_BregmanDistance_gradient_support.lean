-- Prove2me | solution 1 for BregmanDistance.gradient_support
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-26T14:36:13.308079+00:00
-- url     : https://prove2.me/submissions/dff60848-7691-4630-beaa-b1f69b4b2c6c

import Mathlib
import Definitions.Def_BregmanPPA_Convergence_Model


set_option autoImplicit false
open BregmanPPA.Convergence ThreeOpSplitting.Convergence Filter Topology

-- carved from submission 4d2c4647-a5d0-4c8f-a57b-22839b2fb74b, lines 1126-1140

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] (S : Set H) (h : H → ℝ)
    (hh : IsBregmanFunction S h) {y z : H} (hy : y ∈ S) (hz : z ∈ closure S) :
    inner ℝ (gradient h y) (z - y) ≤ h z - h y := by
  have hd : DifferentiableAt ℝ h y :=
    ((hh.contDiffOn.differentiableOn (by simp)) y hy).differentiableAt (hh.isOpen.mem_nhds hy)
  let l : ℝ →ᵃ[ℝ] H := AffineMap.lineMap y z
  have hcv := hh.strictConvexOn.convexOn.comp_affineMap l
  have h0 : (0 : ℝ) ∈ l ⁻¹' closure S := by simpa [l] using subset_closure hy
  have h1 : (1 : ℝ) ∈ l ⁻¹' closure S := by simpa [l] using hz
  have hder : HasDerivAt (h ∘ l) (fderiv ℝ h y (z-y)) 0 := by
    apply hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ)
      (AffineMap.hasDerivAt_lineMap (a := y) (b := z) (x := (0 : ℝ)))
    simp [l]
  have hs := hcv.le_slope_of_hasDerivAt h0 h1 (by norm_num) hder
  simpa [l,slope,inner_gradient_left] using hs
