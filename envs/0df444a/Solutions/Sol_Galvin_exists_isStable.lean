-- Prove2me | solution 1 for Galvin.exists_isStable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:29:40.743959+00:00
-- url     : https://prove2.me/submissions/46b0db68-b0d6-48d5-b4e2-041be146ca70

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Choose
public import Mathlib.Data.Set.Card
public import Definitions.Def_GalvinLib_GaleShapley
public import Theorems.Thm_Galvin_exists_isTop
public import Theorems.Thm_Galvin_isStable_of_removal

set_option autoImplicit true
@[expose] public section
public section
open Galvin
namespace Galvin
theorem _root_.solution {M W : Type*} [Finite M] [Finite W]
    (rm : M → W → ℕ) (rw : W → M → ℕ) (hrm : ∀ m, Function.Injective (rm m))
    (hrw : ∀ w, Function.Injective (rw w)) :
    ∀ (n : ℕ) (E : M → W → Prop), {p : M × W | E p.1 p.2}.ncard = n →
      ∃ μ, IsStable E rm rw μ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro E hn
  by_cases hsh : ∃ m₁ m₂ w, m₁ ≠ m₂ ∧ IsTop E rm m₁ w ∧ IsTop E rm m₂ w
  · obtain ⟨m₁, m₂, w, hne, h₁, h₂⟩ := hsh
    have key : ∀ a b : M, a ≠ b → IsTop E rm a w → IsTop E rm b w → rw w a < rw w b →
        ∃ μ, IsStable E rm rw μ := by
      intro a b hab ha hb hlt
      let E' : M → W → Prop := fun m v => E m v ∧ ¬ (m = b ∧ v = w)
      have hlt' : {p : M × W | E' p.1 p.2}.ncard < n := by
        rw [← hn]
        apply Set.ncard_lt_ncard _ (Set.toFinite _)
        refine ⟨fun p hp => hp.1, fun h => ?_⟩
        have := h (show (b, w) ∈ {p : M × W | E p.1 p.2} from hb.1)
        exact this.2 ⟨rfl, rfl⟩
      obtain ⟨μ, hμ⟩ := ih _ hlt' E' rfl
      exact ⟨μ, isStable_of_removal E rm rw ha hlt μ hμ hab⟩
    rcases lt_or_gt_of_ne (fun h => hne (hrw w h)) with h | h
    · exact key m₁ m₂ hne h₁ h₂ h
    · exact key m₂ m₁ (Ne.symm hne) h₂ h₁ h
  · push Not at hsh
    refine ⟨IsTop E rm, fun m w h => h.1, fun m w w' h h' => ?_, fun m m' w h h' => ?_,
      fun m w hE hnot => ?_⟩
    · exact hrm m (le_antisymm (h.2 _ h'.1) (h'.2 _ h.1))
    · by_contra hc
      exact hsh m m' w hc h h'
    · obtain ⟨w', hw'⟩ := exists_isTop E rm m w hE
      left
      refine ⟨w', hw', lt_of_le_of_ne (hw'.2 w hE) fun heq => ?_⟩
      rw [hrm m heq] at hw'
      exact hnot hw'
end Galvin
