-- Prove2me | solution 1 for ConvexAnalysis.gauge_radius_frontier
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:08:22.376912+00:00
-- url     : https://prove2.me/submissions/df2a7969-3697-43bf-88c6-95a51b4c6f5d

import Definitions.Def_BirkhoffGlobalSection_ConvexRegularizationModel
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.LocallyConvex.Separation

open BirkhoffGlobalSection Filter Set
open scoped ContDiff Topology


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution (K : Set Phase) (hK : Convex ℝ K)
    (h0 : K ∈ nhds (0 : Phase)) (hb : Bornology.IsVonNBounded ℝ K)
    (x : Phase) (hx : x ≠ 0) : (gauge K x)⁻¹ • x ∈ frontier K := by
  have hg : 0 < gauge K x := (gauge_pos (absorbent_nhds_zero h0) hb).2 hx
  apply (gauge_eq_one_iff_mem_frontier hK h0).mp
  rw [gauge_smul_of_nonneg (inv_nonneg.mpr hg.le), smul_eq_mul,
    inv_mul_cancel₀ hg.ne']
