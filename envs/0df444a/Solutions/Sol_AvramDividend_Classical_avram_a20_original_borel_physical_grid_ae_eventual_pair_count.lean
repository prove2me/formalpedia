-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_original_borel_physical_grid_ae_eventual_pair_count
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T17:22:10.262076+00:00
-- url     : https://prove2.me/submissions/abf1644f-7af5-414c-9ab5-c3654b79ad28

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a20_finite_original_chronological_pair_ncard_eq_finset
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_borel_physical_ceiling_grid_pair_count_exact
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_ceil_grid_pair_count_le_chronological
import Theorems.Thm_AvramDividend_Classical_avram_a20_finite_event_ceiling_grid_eventually_exact_chronological_pairs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : ℝ≥0) (hT : 0 < T)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hS : ({u : ℝ≥0 |
      0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ B}).Finite) :
    let S : Set ℝ≥0 := {u : ℝ≥0 |
      0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ B}
    let K : ℕ := ((S ×ˢ S) ∩
      {p : ℝ≥0 × ℝ≥0 | p.1 < p.2}).ncard
    let N : ℝ≥0 → ℝ≥0 → ℝ≥0∞ := fun a b =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc a b ×ˢ B)
    let A : ℕ → ℝ≥0∞ := fun k =>
      ∑ i : Fin k,
        N 0 (((i.val : ℝ≥0) * T) / (k : ℝ≥0)) *
        N (((i.val : ℝ≥0) * T) / (k : ℝ≥0))
          ((((i.val + 1 : ℕ) : ℝ≥0) * T) / (k : ℝ≥0))
    (∀ k, A k ≤ (K : ℝ≥0∞)) ∧
    (∀ᶠ k in atTop, A k = (K : ℝ≥0∞)) := by
  classical
  intro S K N A
  let F : Finset ℝ≥0 := hS.toFinset
  have hF : ∀ u ∈ F, 0 < u ∧ u ≤ T := by
    intro u hu
    have hm := (hS.mem_toFinset).mp hu
    exact ⟨hm.1, hm.2.1⟩
  have hK : K =
      ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card := by
    simpa only [K, S, F] using
      (avram_a20_finite_original_chronological_pair_ncard_eq_finset S hS)
  have hGrid (k : ℕ) (hk : 0 < k) :
      A k = (((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 =>
        Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) <
        Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ)))).card : ℝ≥0∞) := by
    simpa only [A, N, F, S] using
      (avram_a20_original_borel_physical_ceiling_grid_pair_count_exact
        X ω T hT B hB hS k hk).symm
  constructor
  · intro k
    by_cases hk : 0 < k
    · rw [hGrid k hk, hK]
      exact_mod_cast
        (avram_p4_f_assembly_original_ceil_grid_pair_count_le_chronological
          F T hT k)
    · have hz : k = 0 := Nat.eq_zero_of_not_pos hk
      subst k
      simp [A]
  · obtain ⟨k₀, hk₀, hEqual⟩ :=
      avram_a20_finite_event_ceiling_grid_eventually_exact_chronological_pairs
        F T hT
    filter_upwards [eventually_ge_atTop k₀] with k hk
    have hkpos : 0 < k := lt_of_lt_of_le hk₀ hk
    rw [hGrid k hkpos, hK]
    exact congrArg (fun E : Finset (ℝ≥0 × ℝ≥0) =>
      (E.card : ℝ≥0∞)) (hEqual k hk).symm
