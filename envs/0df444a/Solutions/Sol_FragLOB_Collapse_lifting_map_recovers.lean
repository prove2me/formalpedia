-- Prove2me | solution 1 for FragLOB.Collapse.lifting_map_recovers
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:28:01.83969+00:00
-- url     : https://prove2.me/submissions/be25c30c-8e8a-4500-950d-a25106795b68

import Mathlib
import Definitions.Def_FragLOB_Collapse_Model

open MeasureTheory

open FragLOB.Collapse in
theorem solution {N : ℕ} (M : Market N) (hM : M.Standing) (F : Measure ℝ)
    [IsProbabilityMeasure F] (hF : F (Set.Iio 0) = 0) (pi : ℝ → Fin (N + 1) → ℝ)
    (Q : Fin N → ℝ) (hEq : IsEquilibrium M F pi Q) :
    Q = lift M F pi (workload M Q) := by
  obtain ⟨_, _, hW, _, hbal⟩ := hEq
  obtain ⟨_, _, hmu, hbeta⟩ := hM
  funext i
  unfold lift
  rw [hbal i]
  unfold marketRate
  have hb := hbeta i
  have h1 : M.mu * M.beta i ≠ 0 := (mul_pos hmu hb).ne'
  field_simp
