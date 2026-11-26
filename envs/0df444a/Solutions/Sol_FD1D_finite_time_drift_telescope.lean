-- Prove2me | solution 1 for FD1D.finite_time_drift_telescope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:07:08.191246+00:00
-- url     : https://prove2.me/submissions/82a214dc-10cd-4c78-b21f-b6cc2c6f2caf

import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Drift
import Definitions.Def_FD1D_Potential

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators
namespace FD1D
theorem _root_.solution
    (T : ℕ) (Phi D R : ℕ → ℝ)
    (hdrift : ∀ t < T, Phi (t + 1) - Phi t = D t - R t) :
    ∑ t ∈ Finset.range T, D t =
      ∑ t ∈ Finset.range T, R t + Phi T - Phi 0 := by
  have hsum :
      ∑ t ∈ Finset.range T, (Phi (t + 1) - Phi t) =
        ∑ t ∈ Finset.range T, (D t - R t) := by
    apply Finset.sum_congr rfl
    intro t ht
    exact hdrift t (Finset.mem_range.mp ht)
  rw [Finset.sum_range_sub, Finset.sum_sub_distrib] at hsum
  linarith
end FD1D
