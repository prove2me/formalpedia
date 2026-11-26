-- Prove2me | solution 1 for Eden.singularValueFunction_evolution_on_four_five
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:02:22.729932+00:00
-- url     : https://prove2.me/submissions/158cd241-8d87-4fe4-b8e2-86962c98958b

import Definitions.Def_Eden_SingularValueFunction
import Definitions.Def_Eden_VolumeGrowth
import Definitions.Def_Eden_FiniteTimeDimension
import Theorems.Thm_Eden_singularValueFunction_interpolate
import Theorems.Thm_Eden_singularValues_fderiv_evolution_fifth
import Theorems.Thm_Eden_singularValues_fderiv_evolution_prod_four


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c t d : ℝ}
    (hc : 4 ≤ c) (ht : 0 ≤ t) {p : PhaseSpace} (hp : p ∈ attractor)
    (hd₄ : 4 ≤ d) (hd₅ : d ≤ 5) :
    singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d =
      Real.exp (4 * t - 6 * volumeDefect t p - c * t * (d - 4)) := by
  have h := singularValueFunction_interpolate (fderiv ℝ (evolution c t) p).toLinearMap
    (k := 4) (by norm_num) (α := d - 4) (by linarith) (by linarith)
  norm_num only [Nat.cast_ofNat] at h
  rw [show (4 : ℝ) + (d - 4) = d by ring] at h
  rw [h, singularValues_fderiv_evolution_fifth hc ht hp]
  have hprod := singularValues_fderiv_evolution_prod_four hc ht hp
  rw [Fin.prod_univ_eq_prod_range] at hprod
  rw [hprod, ← Real.exp_mul, ← Real.exp_add]
  congr 1
  ring
end Eden
