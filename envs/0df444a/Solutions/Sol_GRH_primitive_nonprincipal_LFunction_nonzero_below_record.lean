-- Prove2me | solution 1 for GRH.primitive_nonprincipal_LFunction_nonzero_below_record
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T15:08:52.810966+00:00
-- url     : https://prove2.me/submissions/1f3287f9-4ea3-46dc-8ad5-a192a4084d2a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GRH_dirichlet_band_nonzero_iff_cofinal_finite_grids
import Theorems.Thm_GRH_primitive_nonprincipal_below_record_grid_certificates
import Mathlib.Tactic.NormNum

theorem solution
    (d : ℕ) [NeZero d] (ψ : DirichletCharacter ℂ d) (hprim : ψ.IsPrimitive) (hψ : ψ ≠ 1)
    (s : ℂ) (hl : (1/2:ℝ) < s.re) (hr : s.re ≤ (0.8749570698:ℝ)) :
    ψ.LFunction s ≠ 0 := by
  apply (GRH.dirichlet_band_nonzero_iff_cofinal_finite_grids d ψ hψ (0.8749570698:ℝ)
    (by norm_num) (by norm_num)).2 _ s hl hr
  exact GRH.primitive_nonprincipal_below_record_grid_certificates d ψ hprim hψ
