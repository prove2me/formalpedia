-- Prove2me | solution 1 for Eden.spectrumInterpolation_mono_spectrum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:02:16.677456+00:00
-- url     : https://prove2.me/submissions/3f2fe7ac-84dc-4427-8bb6-59796d1a0a62

import Definitions.Def_Eden_PeriodicGap
import Definitions.Def_Eden_ExteriorCocycle
import Definitions.Def_Eden_PeriodicGlobalGrowth
import Theorems.Thm_Eden_singularWeight_bounds


set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden
namespace Eden
theorem _root_.solution {a b : Fin 5 → ℝ}
    (h : ∀ i, a i ≤ b i) (d : ℝ) : spectrumInterpolation a d ≤ spectrumInterpolation b d := by
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (h i)
    (singularWeight_bounds i d).1)
end Eden
