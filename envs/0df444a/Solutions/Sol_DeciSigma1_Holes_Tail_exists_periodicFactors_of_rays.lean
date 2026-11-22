-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.exists_periodicFactors_of_rays
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:03:16.432794+00:00
-- url     : https://prove2.me/submissions/70d82ecf-afd0-433e-8972-4030fb62e93e

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RayCompatibility
public import Mathlib.Order.Nat
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Candidates
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_period_pos
public import Theorems.Thm_DeciSigma1_Holes_Tail_NoSuffixOccurrenceEndsBetween_mono
public import Theorems.Thm_DeciSigma1_Holes_Tail_PeriodicCover_mono
public import Theorems.Thm_DeciSigma1_Holes_Tail_periodicOn_of_rayAgrees
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_nil
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_Words_ChainBoundFrom_mono
public import Theorems.Thm_DeciSigma1_Words_ChainBound_mono
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_trans
public import Theorems.Thm_DeciSigma1_Words_PeriodicOn_mono
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_Words_length_suffixOfLength
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_cons_cons
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_nil
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_singleton
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Holes.Tail.suffixLengthBound_nil
attribute [local simp] DeciSigma1.Holes.Tail.suffixLengthEnvelope_nil
attribute [local simp] DeciSigma1.Words.Ray.length_suffixBeforeOnset
attribute [local simp] DeciSigma1.Words.length_suffixOfLength
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Arithmetic DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Automata DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
namespace DeciSigma1.Holes.Tail
theorem _root_.solution [DecidableEq α] {ι : Type*} (s : Finset ι)
    (Ω : ι → Ray α) (E : ι → ℕ) {x : List α} {P cap : ℕ}
    (hag : ∀ i ∈ s, RayAgrees (Ω i) x (E i)) (hP : ∀ i ∈ s, (Ω i).period ≤ P)
    (hcap : cap ≤ x.length) :
    ∃ fs : List PeriodicFactor, fs.length = (s.image fun i => (Ω i).onset).card ∧
      (∀ f ∈ fs, f.Valid x P ∧ f.stop ≤ cap) ∧
      ∀ i ∈ s, ∀ y, (Ω i).onset ≤ y → y < E i → y < cap → Covers fs y := by
  classical
  -- for each onset, the end and the period of a ray with that onset reaching furthest
  have hbest : ∀ a, ∃ e p : ℕ, a ∈ s.image (fun i => (Ω i).onset) → ∃ i ∈ s,
      (Ω i).onset = a ∧ E i = e ∧ (Ω i).period = p ∧ ∀ j ∈ s, (Ω j).onset = a → E j ≤ e := by
    intro a
    by_cases ha : a ∈ s.image fun i => (Ω i).onset
    · obtain ⟨i0, hi0, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨i, hi, hmax⟩ := (s.filter fun j => (Ω j).onset = (Ω i0).onset).exists_max_image E
        ⟨i0, Finset.mem_filter.mpr ⟨hi0, rfl⟩⟩
      rw [Finset.mem_filter] at hi
      exact ⟨E i, (Ω i).period, fun _ => ⟨i, hi.1, hi.2, rfl, rfl,
        fun j hj hja => hmax j (Finset.mem_filter.mpr ⟨hj, hja⟩)⟩⟩
    · exact ⟨0, 0, fun h => absurd h ha⟩
  choose e p hep using hbest
  refine ⟨(s.image fun i => (Ω i).onset).toList.map fun a => ⟨a, min (e a) cap, p a⟩,
    by simp, fun f hf => ?_, fun i hi y hy hyE hycap => ?_⟩
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hf
    obtain ⟨i, hi, rfl, hie, hip, -⟩ := hep a (Finset.mem_toList.mp ha)
    rw [← hie, ← hip]
    exact ⟨⟨Ray.period_pos, hP i hi, (min_le_right _ _).trans hcap,
      (periodicOn_of_rayAgrees (hag i hi)).mono le_rfl (min_le_left _ _)⟩, min_le_right _ _⟩
  · have ha : (Ω i).onset ∈ s.image fun i => (Ω i).onset := Finset.mem_image_of_mem _ hi
    obtain ⟨-, -, -, -, -, hmax⟩ := hep _ ha
    exact ⟨_, List.mem_map.mpr ⟨_, Finset.mem_toList.mpr ha, rfl⟩, hy,
      lt_min (hyE.trans_le (hmax i hi rfl)) hycap⟩
end DeciSigma1.Holes.Tail
