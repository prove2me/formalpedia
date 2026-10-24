-- Prove2me | solution 1 for FairGuarantees.DivideChoose.invariant
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T18:54:58.081215+00:00
-- url     : https://prove2.me/submissions/e9b7d5e2-0e87-496c-a07f-ecfe4abdb1b0

import Mathlib
import Definitions.Def_FairGuarantees_DivideChoose_Setting
import Definitions.Def_FairGuarantees_DivideChoose_DCRule

open FairGuarantees.DivideChoose

theorem nextAgents_take_succ' {d n : ℕ} (run : List (DCStep d n)) (k : ℕ) (hk : k < run.length) :
    nextAgents (run.take (k+1)) = run[k].agents \ Matched run[k] := by
  have : (run.take (k+1)).getLast? = some run[k] := by
    rw [List.getLast?_take]
    simp [hk]
  simp [nextAgents, this]

theorem nextAgents_antitone' {d n : ℕ} {Ω : Set (E d)} (run : List (DCStep d n))
    (hrun : IsValidPrefix Ω run) :
    ∀ m j, j + m = run.length → nextAgents run ⊆ nextAgents (run.take j) := by
  intro m
  induction m with
  | zero => intro j hj; simp at hj; subst hj; simp
  | succ m ih =>
    intro j hj
    have hjl : j < run.length := by omega
    have h1 := ih (j+1) (by omega)
    rw [nextAgents_take_succ' run j hjl] at h1
    rw [← (hrun j hjl).1]
    exact h1.trans Finset.sdiff_subset

theorem solution {d n : ℕ} (hn : 0 < n) {Ω : Set (E d)} {u : Set (E d) → ℝ} (i : Fin n)
    (run : List (DCStep d n)) (hrun : IsValidPrefix Ω run)
    (hstrat : FollowsMinMaxStrategy Ω u i run) (hi : i ∈ nextAgents run) :
    ∀ s ∈ run, ∀ a ∈ Matched s, u (assignedPart s a) < minMax Ω u n := by
  intro s hs a ha
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hs
  have hi' : i ∈ run[k].agents \ Matched run[k] := by
    rw [← nextAgents_take_succ' run k hk]
    exact nextAgents_antitone' run hrun (run.length - (k+1)) (k+1) (by omega) hi
  rw [Finset.mem_sdiff] at hi'
  obtain ⟨hiA, hiM⟩ := hi'
  obtain ⟨-, -, -, -, -, -, ⟨f, hf, hpm⟩, hdiv, -⟩ := (hrun k hk).2.2
  have hnd : ¬ IsDivider run[k] i := fun h => hiM (hdiv i h)
  have hlik := (hstrat run[k] hs hiA).2 hnd
  have hnot : ¬ run[k].likes i (f a) :=
    hpm.2.2.2.2 i (Finset.mem_sdiff.mpr ⟨hiA, hiM⟩) (f a) (Finset.mem_image_of_mem f ha)
  rw [hlik] at hnot
  have hass : assignedPart run[k] a = run[k].parts (f a) := by
    simp [assignedPart, hf a ha]
  rw [hass]
  exact lt_of_not_ge hnot
