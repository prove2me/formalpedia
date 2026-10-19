-- Prove2me | solution 1 for ExecCompLP.LAD.project_feasible
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-17T16:44:57.993986+00:00
-- url     : https://prove2.me/submissions/0f710fab-38d8-4fa7-96c3-21d1d612c3d9

import Definitions.Def_ExecCompLP_LAD_Setting

open ExecCompLP.LAD

local notation "posPart" => ExecCompLP.LAD.posPart
local notation "negPart" => ExecCompLP.LAD.negPart

theorem solution {n L : ℕ} [NeZero L]
    (x : Fin n → Fin L → ℝ) (sM sm : ℝ) (K : Finset (Fin L))
    (s : Fin L → ℝ) (a : Fin n → ℝ) (u v : Fin L → ℝ)
    (h : LPFeasible x sM sm K s a u v) :
    Feasible x sM sm a ∧ obj x K s a ≤ lpObj K u v := by
  refine ⟨h.1, Finset.sum_le_sum ?_⟩
  intro k hk
  obtain ⟨hu, hv, heq⟩ := h.2 k hk
  rw [heq]
  apply abs_le.mpr
  constructor <;> linarith

