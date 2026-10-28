-- Prove2me | solution 1 for FragLOB.Collapse.eq_12
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T02:16:50.346859+00:00
-- url     : https://prove2.me/submissions/ffca717d-dccf-42d0-a355-43abbbd3fc72

import Mathlib
import Definitions.Def_FragLOB_Collapse_Model

open MeasureTheory FragLOB.Collapse

theorem solution {N : ℕ} (M : Market N) (hM : M.Standing) (Q : Fin N → ℝ)
    (hQ : ∀ i, 0 ≤ Q i) (hW : 0 < workload M Q) :
    ∀ i, delay M Q i = workload M Q / (M.mu * M.beta i) := by
  intro i
  obtain ⟨-, -, hmu, hb⟩ := hM
  have hbi := hb i
  unfold delay
  split_ifs with h
  · unfold marketRate
    have hne : workload M Q ≠ 0 := hW.ne'
    field_simp
  · rfl
