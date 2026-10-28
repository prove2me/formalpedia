-- Prove2me | solution 1 for AvramDividend.Classical.joint_reserve_closed_survival_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T07:31:20.350765+00:00
-- url     : https://prove2.me/submissions/2924c036-de21-433d-9128-420bf48203e0

import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_lower_survival_closed_grid_iff

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Closed-horizon survival is jointly measurable in reserve and sample path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) :
    MeasurableSet {p : ℝ × Ω |
      ∀ t : ℝ≥0, t ≤ T → 0 ≤ p.1 + X.X t p.2} := by
  have hXm : ∀ t, Measurable (fun p : ℝ × Ω => X.X t p.2) :=
    fun t => ((X.adapted t).mono (𝓕.le t) le_rfl).comp measurable_snd
  have hH : Measurable (fun p : ℝ × Ω => p.1) := measurable_fst
  have e : {p : ℝ × Ω | ∀ t : ℝ≥0, t ≤ T →
      0 ≤ p.1 + X.X t p.2} =
      (⋂ n : ℕ, ⋂ k : ℕ, {p : ℝ × Ω |
        0 < n → (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < T →
          0 ≤ p.1 + X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) p.2}) ∩
        {p : ℝ × Ω | 0 ≤ p.1 + X.X T p.2} := by
    ext p
    rw [Set.mem_setOf_eq,
      chat04_random_reserve_lower_survival_closed_grid_iff
        X (fun _ : Ω => p.1) p.2 T]
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    exact ⟨fun ⟨h1, h2⟩ => ⟨fun n k hn hk => h1 n hn k hk, h2⟩,
      fun ⟨h1, h2⟩ => ⟨fun n hn k hk => h1 n k hn hk, h2⟩⟩
  rw [e]
  refine MeasurableSet.inter
    (MeasurableSet.iInter fun n => MeasurableSet.iInter fun k => ?_)
    (measurableSet_le measurable_const (hH.add (hXm T)))
  by_cases hn : 0 < n
  · by_cases hk : (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < T
    · simp only [hn, hk, true_implies]
      exact measurableSet_le measurable_const (hH.add (hXm _))
    · simp [hk]
  · simp [hn]
