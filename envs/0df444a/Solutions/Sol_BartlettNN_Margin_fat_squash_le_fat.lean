-- Prove2me | solution 1 for BartlettNN.Margin.fat_squash_le_fat
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T12:43:07.244984+00:00
-- url     : https://prove2.me/submissions/66909a6f-8d7b-4a50-910d-801a097e912e

import Mathlib
import Definitions.Def_BartlettNN_Margin_Classification
import Definitions.Def_BartlettNN_Margin_FatShattering
import Definitions.Def_BartlettNN_Margin_Squash
import Definitions.Def_BartlettNN_Margin_Covering

open MeasureTheory

set_option autoImplicit false

open BartlettNN.Margin in
theorem efda2dd7_shatters_of_squash {X : Type*} (H : Set (X → ℝ)) (γ δ : ℝ) (hγ : 0 < γ)
    (hδ : 0 < δ) {m : ℕ} (x : Fin m → X) (hs : GammaShatters (squashClass γ H) δ x) :
    GammaShatters H δ x := by
  obtain ⟨r, hr⟩ := hs
  have hlo : ∀ i, -γ + δ ≤ r i := by
    intro i
    obtain ⟨g, ⟨h, _, rfl⟩, hg⟩ := hr (fun _ => false)
    have h1 := hg i
    simp only [pm, Function.comp, squash] at h1
    have h2 : -γ ≤ max (-γ) (min γ (h (x i))) := le_max_left _ _
    simp at h1
    linarith
  have hhi : ∀ i, r i ≤ γ - δ := by
    intro i
    obtain ⟨g, ⟨h, _, rfl⟩, hg⟩ := hr (fun _ => true)
    have h1 := hg i
    simp only [pm, Function.comp, squash] at h1
    have h2 : max (-γ) (min γ (h (x i))) ≤ γ := max_le (by linarith) (min_le_left _ _)
    simp at h1
    linarith
  refine ⟨r, fun b => ?_⟩
  obtain ⟨g, ⟨h, hH, rfl⟩, hg⟩ := hr b
  refine ⟨h, hH, fun i => ?_⟩
  have h1 := hg i
  have lo := hlo i
  have hi := hhi i
  cases hb : b i with
  | false =>
    simp only [hb, pm, Function.comp, squash] at h1 ⊢
    simp at h1 ⊢
    have h3 : min γ (h (x i)) ≤ r i - δ := le_trans (le_max_right _ _) (by linarith)
    rcases min_le_iff.mp h3 with h4 | h4 <;> linarith
  | true =>
    simp only [hb, pm, Function.comp, squash] at h1 ⊢
    simp at h1 ⊢
    have h3 : r i + δ ≤ max (-γ) (min γ (h (x i))) := by linarith
    rcases le_max_iff.mp h3 with h4 | h4
    · linarith
    · have := (le_min_iff.mp h4).2
      linarith

open BartlettNN.Margin in
theorem solution {X : Type*} (H : Set (X → ℝ)) (γ : ℝ) (hγ : 0 < γ) :
    fat (squashClass γ H) (γ / 16) ≤ fat H (γ / 16) := by
  unfold fat
  refine iSup_le fun m => iSup_le fun x => iSup_le fun hs => ?_
  exact le_iSup_of_le m (le_iSup_of_le x (le_iSup_of_le
    (efda2dd7_shatters_of_squash H γ (γ / 16) hγ (by positivity) x hs) le_rfl))
