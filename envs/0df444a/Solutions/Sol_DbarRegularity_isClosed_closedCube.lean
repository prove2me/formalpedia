-- Prove2me | solution 1 for DbarRegularity.isClosed_closedCube
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-11T23:51:13.416267+00:00
-- url     : https://prove2.me/submissions/090396b4-b0fd-4407-a0c9-5c48cdda100d

import Definitions.Def_DbarRegularity_Setting
import Theorems.Thm_DbarRegularity_closedCube_eq_preimage



namespace DbarRegularity

open MeasureTheory Metric Filter Topology Set
open scoped ENNReal NNReal

theorem isClosed_closedCube {d : ℕ} (a : EuclideanSpace ℝ (Fin d)) (s : ℝ) :
    IsClosed (closedCube a s) := by
  rw [closedCube_eq_preimage]
  exact isClosed_Icc.preimage (PiLp.continuous_ofLp 2 _)

end DbarRegularity

open DbarRegularity

theorem solution {d : ℕ} (a : EuclideanSpace ℝ (Fin d)) (s : ℝ) :
    IsClosed (closedCube a s) :=
  isClosed_closedCube a s
