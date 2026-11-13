-- Prove2me | solution 1 for BosonicLearn.fockPOVM_reindex
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T05:40:20.622203+00:00
-- url     : https://prove2.me/submissions/ae236af5-7caa-48e5-b0c5-79cdcdeb5472

import Mathlib
import Definitions.Def_BosonicLearn_FockPOVM
import Theorems.Thm_BosonicLearn_isDensity_reindex

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)
open MeasureTheory
open scoped ENNReal Matrix

open BosonicLearn

noncomputable section

theorem solution {J J' Ω : Type} [DecidableEq J] [DecidableEq J'] [MeasurableSpace Ω]
    (M : FockPOVM J Ω) (e : J ≃ J') :
    ∃ M' : FockPOVM J' Ω, ∀ ρ : Matrix J J ℂ, IsDensity ρ →
      M'.law (fun i j => ρ (e.symm i) (e.symm j)) = M.law ρ := by
  -- relabelling back a density operator on `ℓ²(J')` gives a density operator on `ℓ²(J)`
  have hden : ∀ ρ' : Matrix J' J' ℂ, IsDensity ρ' → IsDensity (fun i j : J => ρ' (e i) (e j)) := by
    intro ρ' h
    have h' := isDensity_reindex e.symm h
    simpa using h'
  refine ⟨{
    effect := fun B i j => M.effect B (e.symm i) (e.symm j)
    effect_form := ?_
    effect_univ := ?_
    law := fun ρ' => M.law (fun i j => ρ' (e i) (e j))
    law_prob := fun ρ' h => M.law_prob _ (hden ρ' h)
    law_born := ?_ }, ?_⟩
  · intro B hB s z
    have h := M.effect_form B hB (s.map e.symm.toEmbedding) (fun a => z (e a))
    simpa [Finset.sum_map] using h
  · funext i j
    simp [M.effect_univ, Matrix.one_apply]
  · intro ρ' h B hB
    rw [M.law_born _ (hden ρ' h) B hB]
    congr 2
    rw [← Equiv.tsum_eq e.symm]
    refine tsum_congr fun i' => ?_
    rw [← Equiv.tsum_eq e.symm]
    refine tsum_congr fun j' => ?_
    simp
  · intro ρ _
    simp
