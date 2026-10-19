-- Prove2me | solution 1 for ExecCompLP.LAD.lp_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-17T17:04:41.46023+00:00
-- url     : https://prove2.me/submissions/30e7e605-2966-4532-a20a-b50f9e020d43

import Theorems.Thm_ExecCompLP_LAD_minimal_values_eq
import Theorems.Thm_ExecCompLP_LAD_lift_feasible
import Theorems.Thm_ExecCompLP_LAD_project_feasible
import Definitions.Def_ExecCompLP_LAD_Setting

open ExecCompLP.LAD

local notation "posPart" => ExecCompLP.LAD.posPart
local notation "negPart" => ExecCompLP.LAD.negPart

lemma lad_min_project {n L : ℕ} [NeZero L]
    (x : Fin n → Fin L → ℝ) (sM sm : ℝ) (K : Finset (Fin L))
    (s : Fin L → ℝ) (a : Fin n → ℝ) (u v : Fin L → ℝ)
    (h : IsLPMinimizer x sM sm K s a u v) : IsMinimizer x sM sm K s a := by
  obtain ⟨ha, hle⟩ := ExecCompLP.LAD.project_feasible x sM sm K s a u v h.1
  refine ⟨ha, ?_⟩
  intro a' ha'
  obtain ⟨hf', heq'⟩ := ExecCompLP.LAD.lift_feasible x sM sm K s a' ha'
  exact hle.trans ((h.2 a' _ _ hf').trans heq'.le)

theorem solution {n L : ℕ} [NeZero L]
    (x : Fin n → Fin L → ℝ) (sM sm : ℝ) (K : Finset (Fin L))
    (s : Fin L → ℝ) :
    (∀ t : ℝ,
      (∃ a : Fin n → ℝ, Feasible x sM sm a ∧ obj x K s a ≤ t) ↔
      (∃ (a : Fin n → ℝ) (u v : Fin L → ℝ),
        LPFeasible x sM sm K s a u v ∧ lpObj K u v ≤ t)) ∧
    (∀ a : Fin n → ℝ,
      IsMinimizer x sM sm K s a ↔
      IsLPMinimizer x sM sm K s a
        (fun k => posPart (salary x a k - s k))
        (fun k => negPart (salary x a k - s k))) ∧
    (∀ (a : Fin n → ℝ) (u v : Fin L → ℝ),
      IsLPMinimizer x sM sm K s a u v → IsMinimizer x sM sm K s a) := by
  refine ⟨ExecCompLP.LAD.minimal_values_eq x sM sm K s, ?_, lad_min_project x sM sm K s⟩
  intro a
  constructor
  · intro h
    obtain ⟨hf, heq⟩ := ExecCompLP.LAD.lift_feasible x sM sm K s a h.1
    refine ⟨hf, ?_⟩
    intro a' u' v' h'
    obtain ⟨ha', hle'⟩ := ExecCompLP.LAD.project_feasible x sM sm K s a' u' v' h'
    exact heq.le.trans ((h.2 a' ha').trans hle')
  · exact lad_min_project x sM sm K s a _ _
