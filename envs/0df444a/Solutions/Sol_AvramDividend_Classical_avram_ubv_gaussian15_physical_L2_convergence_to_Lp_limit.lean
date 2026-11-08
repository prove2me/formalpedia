-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gaussian15_physical_L2_convergence_to_Lp_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T16:44:43.366966+00:00
-- url     : https://prove2.me/submissions/0fab3641-307e-40b7-be5a-8a25451b6e68

import Mathlib.MeasureTheory.Function.LpSpace.Complete

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

/-- Original physical eLpNorm convergence of square-integrable Gaussian
grids yields convergence of their canonical Lp classes. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (Q : ℕ → Ω → ℝ) (L : Ω → ℝ)
    (hQ : ∀ n, MemLp (Q n) 2 P) (hL : MemLp L 2 P)
    (hConv : Tendsto (fun n => eLpNorm (Q n - L) 2 P)
      atTop (𝓝 0)) :
    Tendsto (fun n => (hQ n).toLp (Q n))
      atTop (𝓝 (hL.toLp L)) := by
  let F : ℕ → Lp ℝ 2 P := fun n => (hQ n).toLp (Q n)
  let Z : Lp ℝ 2 P := hL.toLp L
  have heq (n : ℕ) :
      eLpNorm ((F n : Ω → ℝ) - (Z : Ω → ℝ)) 2 P =
        eLpNorm (Q n - L) 2 P := by
    apply eLpNorm_congr_ae
    filter_upwards [(hQ n).coeFn_toLp, hL.coeFn_toLp] with ω hn hZ
    change F n ω - Z ω = Q n ω - L ω
    rw [hn, hZ]
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' F Z).2
  simpa only [heq] using hConv
