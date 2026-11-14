-- Prove2me | solution 1 for AvramDividend.Classical.avram_b205_original_canonical_grid_marked_count_measurable_and_real_poisson_dom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:28:22.43242+00:00
-- url     : https://prove2.me/submissions/9a5c759e-3612-43df-a1cb-b66871c2908c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b181_original_random_grid_genuine_marked_source_card_measurable
import Theorems.Thm_AvramDividend_Classical_avram_b163_original_true_marked_monotone_grid_card_le_full_negative_poisson
import Theorems.Thm_AvramDividend_Classical_avram_b195_original_fullnegative_poisson_count_finite_ae_from_source_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Actual original marked-cell measurability and conull real full-negative source domination. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (T : ℝ≥0) (hT : T ≤ (n : ℝ≥0))
    (S : Finset ℕ)
    (grid : Ω → ℕ → ℝ≥0)
    (hMono : ∀ ω, Monotone (grid ω))
    (hGridMeas : ∀ i, Measurable (fun ω => grid ω i))
    (hHorizon : ∀ ω i, i ∈ S → grid ω (i + 1) ≤ T)
    (hCountMeas : AEMeasurable (fun ω : Ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ))) P) :
    let J : Ω → Finset ℕ := fun ω => by
      classical
      exact S.filter (fun i => ∃ u : ℝ≥0,
        grid ω i < u ∧ u ≤ grid ω (i + 1) ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0)
    Measurable (fun ω => ((J ω).card : ℝ)) ∧
    (∀ᵐ ω ∂P, ((J ω).card : ℝ) ≤
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ))).toReal) := by
  classical
  intro J
  have hJM : Measurable (fun ω => ((J ω).card : ℝ)) := by
    have hm :=
      avram_b181_original_random_grid_genuine_marked_source_card_measurable
        X S (fun i ω => grid ω i) (fun i ω => grid ω (i + 1))
        hGridMeas (fun i => hGridMeas (i + 1))
        (fun ω i => hMono ω (Nat.le_succ i))
    simpa only [J] using hm
  let M : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iio (0 : ℝ))
  have hFiniteAE : ∀ᵐ ω ∂P, M ω < ⊤ := by
    have hm := avram_b195_original_fullnegative_poisson_count_finite_ae_from_source_L1
      X hFinite n (fun _ : Ω => T) (fun _ => hT)
      (by simpa only [M] using hCountMeas)
    simpa only [M] using hm
  have hWitness (ω : Ω) (i : ℕ) (hi : i ∈ J ω) :
      ∃ u : ℝ≥0,
        grid ω i < u ∧ u ≤ grid ω (i + 1) ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 := by
    exact (Finset.mem_filter.mp hi).2
  have hRange (ω : Ω) (i : ℕ) (hi : i ∈ J ω) :
      grid ω (i + 1) ≤ T :=
    hHorizon ω i (Finset.mem_filter.mp hi).1
  refine ⟨hJM, ?_⟩
  filter_upwards [hFiniteAE] with ω hω
  have hCardBound :=
    avram_b163_original_true_marked_monotone_grid_card_le_full_negative_poisson
      X ω T (grid ω) (hMono ω) (J ω)
      (hWitness ω) (hRange ω)
  have hReal := ENNReal.toReal_mono (ne_of_lt hω) hCardBound
  simpa only [M, ENNReal.toReal_natCast, Nat.cast_id] using hReal
