-- Prove2me | solution 1 for AvramDividend.Classical.cstar_finite_of_deriv_growth_both_ends
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T18:21:50.016529+00:00
-- url     : https://prove2.me/submissions/85fd59ca-9d48-46e8-82e6-2641cb9e3eef
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_finite_of_nearzero_and_tail_bounds

open AvramDividend.Classical Filter Set
open scoped Topology ENNReal

theorem solution (W : ℝ → ℝ) (a : ℝ) (ha : 0 < a)
    (hcont : ContinuousOn (deriv W) (Set.Ioi 0))
    (hzero : Filter.Tendsto (deriv W) (𝓝[>] (0 : ℝ)) Filter.atTop)
    (hinfty : Filter.Tendsto (deriv W) Filter.atTop Filter.atTop) :
    cstar W < ⊤ := by
  have hnearev :
      {x : ℝ | deriv W a ≤ deriv W x} ∈ 𝓝[>] (0 : ℝ) :=
    hzero.eventually_ge_atTop (deriv W a)
  obtain ⟨δ, hδmem, hδsubset⟩ :=
    (mem_nhdsGT_iff_exists_mem_Ioc_Ioo_subset ha).1 hnearev
  have hδ0 : 0 < δ := hδmem.1
  have hδa : δ ≤ a := hδmem.2
  obtain ⟨R, hR⟩ :=
    Filter.eventually_atTop.1 (hinfty.eventually_ge_atTop (deriv W a))
  let M : ℝ := max a R + 1
  have haM : a < M := by
    dsimp [M]
    have hm := le_max_left a R
    linarith
  have hRM : R ≤ M := by
    dsimp [M]
    have hm := le_max_right a R
    linarith
  have hhalf : 0 < δ / 2 := half_pos hδ0
  have hhalfa : δ / 2 < a := (half_lt_self hδ0).trans_le hδa
  apply cstar_finite_of_nearzero_and_tail_bounds
    W a (δ / 2) M ha hhalf hhalfa haM hcont
  · intro x hx hxδ
    exact hδsubset ⟨hx, hxδ.trans (half_lt_self hδ0)⟩
  · intro x hx
    exact hR x (hRM.trans hx.le)
