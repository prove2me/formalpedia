-- Prove2me | solution 1 for ExecCompLP.LAD.lift_feasible
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-17T16:44:56.198604+00:00
-- url     : https://prove2.me/submissions/85ce18cd-f8fd-4525-893e-02451786666e

import Definitions.Def_ExecCompLP_LAD_Setting

open ExecCompLP.LAD

local notation "posPart" => ExecCompLP.LAD.posPart
local notation "negPart" => ExecCompLP.LAD.negPart

theorem solution {n L : ℕ} [NeZero L]
    (x : Fin n → Fin L → ℝ) (sM sm : ℝ) (K : Finset (Fin L))
    (s : Fin L → ℝ) (a : Fin n → ℝ) (ha : Feasible x sM sm a) :
    LPFeasible x sM sm K s a
      (fun k => posPart (salary x a k - s k))
      (fun k => negPart (salary x a k - s k)) ∧
    lpObj K
      (fun k => posPart (salary x a k - s k))
      (fun k => negPart (salary x a k - s k)) = obj x K s a := by
  constructor
  · refine ⟨ha, ?_⟩
    intro k hk
    dsimp [ExecCompLP.LAD.posPart, ExecCompLP.LAD.negPart]
    refine ⟨le_max_right _ _, le_max_right _ _, ?_⟩
    by_cases h : 0 ≤ salary x a k - s k
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
      ring
    · have h' : salary x a k - s k ≤ 0 := le_of_not_ge h
      rw [max_eq_right h', max_eq_left (neg_nonneg.mpr h')]
      ring
  · apply Finset.sum_congr rfl
    intro k hk
    dsimp [ExecCompLP.LAD.posPart, ExecCompLP.LAD.negPart]
    by_cases h : 0 ≤ salary x a k - s k
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), abs_of_nonneg h]
      ring
    · have h' : salary x a k - s k ≤ 0 := le_of_not_ge h
      rw [max_eq_right h', max_eq_left (neg_nonneg.mpr h'), abs_of_nonpos h']
      ring

