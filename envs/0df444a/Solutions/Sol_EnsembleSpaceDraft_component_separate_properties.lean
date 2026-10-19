-- Prove2me | solution 1 for EnsembleSpaceDraft.component_separate_properties
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T14:31:43.817993+00:00
-- url     : https://prove2.me/submissions/b86fc42d-69d6-4e90-9c2f-fb164f23dcc5

import Definitions.Def_EnsembleSpaceDraft_axioms
import Mathlib

open scoped unitInterval

open EnsembleSpaceDraft

universe u

theorem solution {E : Type u} [TopologicalSpace E] (X : EnsembleSpace E) :
    (∀ e : E, X.IsComponent e e) ∧
      (∀ a b : E, X.IsComponent a b → X.HasCommonComponent a b ∧ ¬ X.Separate a b) ∧
      (∀ a : E, ¬ X.Separate a a) ∧
      (∀ a b : E, X.Separate a b ↔ X.Separate b a) ∧
      (∀ a b : E, X.IsExtreme a → X.IsExtreme b → a ≠ b → X.Separate a b) ∧
      (∀ e a : E, X.IsInternal e → X.HasCommonComponent e a ∧ ¬ X.Separate e a) ∧
      (∀ a b : E, X.Separate a b → X.IsBoundary a ∧ X.IsBoundary b) := by
  have hself : ∀ e : E, X.IsComponent e e := fun e =>
    ⟨1, e, by norm_num, (X.mix_one e e).symm⟩
  have hsymm : ∀ a b : E, X.Separate a b ↔ X.Separate b a := by
    intro a b
    unfold EnsembleSpace.Separate EnsembleSpace.HasCommonComponent
    exact not_congr ⟨fun ⟨c, h1, h2⟩ => ⟨c, h2, h1⟩, fun ⟨c, h1, h2⟩ => ⟨c, h2, h1⟩⟩
  have hint : ∀ e a : E, X.IsInternal e → X.HasCommonComponent e a ∧ ¬ X.Separate e a := by
    intro e a he
    obtain ⟨p, b, hp, hb⟩ := he a
    have hc : X.HasCommonComponent e a := ⟨a, ⟨p, b, hp, hb⟩, hself a⟩
    exact ⟨hc, fun h => h hc⟩
  refine ⟨hself, ?_, ?_, hsymm, ?_, hint, ?_⟩
  · intro a b h
    have hc : X.HasCommonComponent a b := ⟨a, hself a, h⟩
    exact ⟨hc, fun h' => h' hc⟩
  · intro a h
    exact h ⟨a, hself a, hself a⟩
  · rintro a b ha hb hab ⟨c, ⟨p, d, hp, hpa⟩, ⟨q, d', hq, hqb⟩⟩
    have h1 : c = a := ha p c d hp hpa
    have h2 : c = b := hb q c d' hq hqb
    exact hab (h1.symm.trans h2)
  · intro a b h
    refine ⟨fun ha => (hint a b ha).2 h, fun hb => (hint b a hb).2 ((hsymm a b).mp h)⟩

