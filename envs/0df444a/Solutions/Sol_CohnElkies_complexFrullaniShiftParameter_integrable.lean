-- Prove2me | solution 1 for CohnElkies.complexFrullaniShiftParameter_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:24.652437+00:00
-- url     : https://prove2.me/submissions/623bc5ae-8787-4a55-8003-c4a3099e471f

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_complexFrullaniKernel_integrable
import Theorems.Thm_CohnElkies_complexFrullaniShiftKernel_norm_le_exp

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
    {z : ℂ} (hz : 0 < z.re) :
    Integrable
      (Function.uncurry (fun s x : ℝ =>
        complexFrullaniKernel (z + (s : ℂ)) 1 x))
      ((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod
        (volume.restrict (Ioi 0))) := by
  have hm : 0 < min z.re 1 :=
    lt_min hz (by norm_num)
  let C : ℝ := ‖(1 : ℂ) - z‖ + 1
  have hC : 0 ≤ C := by
    try dsimp [C]
    positivity
  have hmeas :
      AEStronglyMeasurable
        (Function.uncurry (fun s x : ℝ =>
          complexFrullaniKernel (z + (s : ℂ)) 1 x))
        ((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod
          (volume.restrict (Ioi 0))) := by
    change
      AEStronglyMeasurable
        (fun p : ℝ × ℝ =>
          (Complex.exp (-(z + (p.1 : ℂ)) * (p.2 : ℂ)) -
            Complex.exp (-(1 : ℂ) * (p.2 : ℂ))) /
              (p.2 : ℂ))
        ((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod
          (volume.restrict (Ioi 0)))
    apply Measurable.aestronglyMeasurable
    fun_prop
  apply (integrable_prod_iff hmeas).2
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_uIoc]
      with s hs
    rw [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hs
    have hspositive : 0 < (z + (s : ℂ)).re := by
      simp only [Complex.add_re, Complex.ofReal_re]
      linarith [hs.1]
    change
      IntegrableOn
        (complexFrullaniKernel (z + (s : ℂ)) 1)
        (Ioi 0)
    exact complexFrullaniKernel_integrable
      hspositive (by norm_num : 0 < (1 : ℂ).re)
  · have hconstant :
        Integrable (fun _ : ℝ => C * (min z.re 1)⁻¹)
          (volume.restrict (Set.uIoc (0 : ℝ) 1)) :=
      intervalIntegrable_iff.mp
        (continuous_const.intervalIntegrable (a := (0 : ℝ))
          (b := 1))
    apply hconstant.mono'
    · simpa only [Function.uncurry_apply_pair] using!
        hmeas.norm.integral_prod_right'
    filter_upwards [ae_restrict_mem measurableSet_uIoc]
      with s hs
    rw [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hs
    have hclosed : s ∈ Icc (0 : ℝ) 1 :=
      ⟨hs.1.le, hs.2⟩
    have hspositive : 0 < (z + (s : ℂ)).re := by
      simp only [Complex.add_re, Complex.ofReal_re]
      linarith [hs.1]
    have hkernel :=
      complexFrullaniKernel_integrable
        hspositive (by norm_num : 0 < (1 : ℂ).re)
    have hmajor :
        IntegrableOn
          (fun x : ℝ =>
            C * Real.exp (-(min z.re 1) * x))
          (Ioi 0) :=
      (laplaceKernel_integrable hm).const_mul C
    change
      ‖∫ x : ℝ in Ioi 0,
        ‖complexFrullaniKernel (z + (s : ℂ)) 1 x‖‖ ≤
          C * (min z.re 1)⁻¹
    rw [Real.norm_eq_abs, abs_of_nonneg
      (integral_nonneg fun x => norm_nonneg
        (complexFrullaniKernel (z + (s : ℂ)) 1 x))]
    calc
      (∫ x : ℝ in Ioi 0,
        ‖complexFrullaniKernel (z + (s : ℂ)) 1 x‖) ≤
          ∫ x : ℝ in Ioi 0,
            C * Real.exp (-(min z.re 1) * x) := by
        apply integral_mono_ae hkernel.norm hmajor
        filter_upwards [ae_restrict_mem measurableSet_Ioi]
          with x hx
        change
          ‖complexFrullaniKernel (z + (s : ℂ)) 1 x‖ ≤
            C * Real.exp (-(min z.re 1) * x)
        exact complexFrullaniShiftKernel_norm_le_exp z
          hclosed hx
      _ = C * (min z.re 1)⁻¹ := by
        rw [integral_const_mul, integral_laplaceKernel hm]
end CohnElkies
