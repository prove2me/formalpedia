-- Prove2me | solution 1 for BirkhoffGlobalSection.left_negative_boundary_compact
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T17:34:26.111369+00:00
-- url     : https://prove2.me/submissions/be6d3728-72e6-44ac-9886-72cb656de190

import Theorems.Thm_BirkhoffGlobalSection_left_negative_boundary_closed
import Theorems.Thm_BirkhoffGlobalSection_left_negative_boundary_bounded
import Mathlib.Topology.MetricSpace.Bounded

open BirkhoffGlobalSection

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    IsCompact
      {s : Phase | s ∈ closure
        (connectedComponentIn
          {t : Phase | leviCivitaHamiltonian μ c t < 0 ∧
            0 < secondCollisionDistanceSq t}
          (fun _ : Fin 4 => (0 : ℝ))) ∧
        leviCivitaHamiltonian μ c s = 0 ∧
        0 < secondCollisionDistanceSq s} := by
  exact Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨left_negative_boundary_closed μ c hμ0 hμ1 hc,
      left_negative_boundary_bounded μ c hμ0 hμ1 hc⟩
