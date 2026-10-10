-- Prove2me | solution 1 for BookProof.SchrodingerCutoff.cutoff_energy_estimate
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T06:20:27.880457+00:00
-- url     : https://prove2.me/submissions/63a5e016-54ed-4cbd-881c-67a173a810d3

-- Generated from ChapterSchrodingerCutoffEsa.lean — solution of BookProof.SchrodingerCutoff.cutoff_energy_estimate
import Mathlib
import Definitions.Def_ChapterSchrodingerCutoffEsa
import Theorems.Thm_BookProof_SchrodingerCutoff_cutoff_energy_core
import Definitions.Def_ChapterParityChirality
open BookProof.SchrodingerCutoff




open MeasureTheory Filter Complex
open BookProof.ChapterParityChirality

set_option maxHeartbeats 1000000 in
theorem solution
    (V : ℝ → ℝ) (hV : Continuous V) (z : ℂ)
    (u u' u'' : ℝ → ℂ)
    (h1 : ∀ x, HasDerivAt u (u' x) x)
    (h2 : ∀ x, HasDerivAt u' (u'' x) x)
    (heq : ∀ x, -u'' x + (V x : ℂ) * u x = z * u x)
    (hVz : ∀ x, 1 ≤ V x - z.re)
    (hL2 : Integrable fun x => ‖u x‖ ^ 2)
    {C : ℝ} (hC : ∀ y, |deriv BookProof.SchrodingerCutoff.chi y| ≤ C)
    {R : ℝ} (hR : 0 < R) :
    ∫ x in Set.Icc (-R) R, ‖u x‖ ^ 2 ≤ 2 * C ^ 2 / R ^ 2 * ∫ x, ‖u x‖ ^ 2 := by
    have hud : Differentiable ℝ u := fun x => (h1 x).differentiableAt
    have hucont : Continuous u := hud.continuous
    refine le_trans ?_ (cutoff_energy_core V hV z u u' u'' h1 h2 heq
      (fun x => le_trans zero_le_one (hVz x)) hL2 hC hR).1
    refine setIntegral_mono_on hL2.integrableOn
      ((by fun_prop : Continuous fun x => (V x - z.re) * ‖u x‖ ^ 2).integrableOn_Icc)
      measurableSet_Icc fun x _ => ?_
    nlinarith [hVz x, sq_nonneg ‖u x‖, norm_nonneg (u x)]

