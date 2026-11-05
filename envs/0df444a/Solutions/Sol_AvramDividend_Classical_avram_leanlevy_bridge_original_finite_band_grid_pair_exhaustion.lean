-- Prove2me | solution 1 for AvramDividend.Classical.avram_leanlevy_bridge_original_finite_band_grid_pair_exhaustion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:09:47.967736+00:00
-- url     : https://prove2.me/submissions/b1106eca-8e30-46d3-b922-9ff68a11faa8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (n : ℕ)
    (F : Finset ℝ≥0)
    (hF : F = (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset)
    (G : ℕ → Finset (ℝ≥0 × ℝ≥0))
    (hSub : ∀ m, G m ⊆ (F ×ˢ F).filter (fun p => p.1 < p.2))
    (hMono : Monotone G)
    (hCover : ∀ p ∈ (F ×ˢ F).filter (fun p => p.1 < p.2),
      ∃ m, p ∈ G m) :
    ∃ N, ∀ m ≥ N, G m = (F ×ˢ F).filter (fun p => p.1 < p.2) := by
  classical
  let R : Finset (ℝ≥0 × ℝ≥0) :=
    (F ×ˢ F).filter (fun p => p.1 < p.2)
  have hFinite :
      ∀ S : Finset (ℝ≥0 × ℝ≥0),
        (∀ p ∈ S, ∃ m, p ∈ G m) →
        ∃ N, ∀ p ∈ S, p ∈ G N := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        intro _
        refine ⟨0, ?_⟩
        intro p hp
        simp at hp
    | @insert p S hpnot ih =>
        intro hc
        obtain ⟨mp, hmp⟩ := hc p (Finset.mem_insert_self p S)
        have hcS : ∀ q ∈ S, ∃ m, q ∈ G m := by
          intro q hq
          exact hc q (Finset.mem_insert_of_mem hq)
        obtain ⟨mS, hmS⟩ := ih hcS
        refine ⟨max mp mS, ?_⟩
        intro q hq
        rcases Finset.mem_insert.mp hq with hqp | hq
        · subst q
          exact (hMono (Nat.le_max_left mp mS)) hmp
        · exact (hMono (Nat.le_max_right mp mS)) (hmS q hq)
  obtain ⟨N, hN⟩ := hFinite R (by simpa [R] using hCover)
  refine ⟨N, ?_⟩
  intro m hm
  apply Finset.Subset.antisymm
  · exact hSub m
  · intro p hp
    exact (hMono hm) (hN p (by simpa [R] using hp))
