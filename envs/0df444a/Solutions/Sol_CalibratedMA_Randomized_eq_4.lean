-- Prove2me | solution 1 for CalibratedMA.Randomized.eq_4
-- status  : ACCEPTED   (prove)
-- author  : @Aaron
-- created : 2026-11-13T18:06:04.893082+00:00
-- url     : https://prove2.me/submissions/8027da6e-d947-4df1-a433-16bf94d0580a

import Definitions.Def_CalibratedMA_Randomized_Rounding

open MeasureTheory

namespace CalibratedMA.Randomized

/-- Clamping has no effect on an admissible score. -/
lemma clamp01_eq_of_mem {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    clamp01 s = s := by
  simp only [clamp01, min_eq_right hs.2, max_eq_right hs.1]

/-- The selected interval contains the score, including at both boundary points. -/
lemma roundIndex_bounds (K M : ℕ) (γ : ℕ → ℝ) (hΓ : IsGridPartition K M γ)
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    roundIndex M γ s < M ∧
      γ (roundIndex M γ s) ≤ s ∧ s ≤ γ (roundIndex M γ s + 1) := by
  classical
  rcases hΓ with ⟨hzero, hone, _, _⟩
  have hM : 0 < M := by
    by_contra h
    have : M = 0 := by omega
    subst M
    linarith
  have hclamp : clamp01 s = s := clamp01_eq_of_mem hs
  let F := (Finset.range M).filter (fun j => γ j ≤ s)
  have hF : F.Nonempty := by
    refine ⟨0, ?_⟩
    simp [F, hM, hzero, hs.1]
  have hjmem : F.sup id ∈ F := by
    simpa only [Set.image_id, Finset.mem_coe] using
      (Finset.sup_mem_of_nonempty (f := id) hF)
  have hj : F.sup id < M ∧ γ (F.sup id) ≤ s := by
    simpa only [F, Finset.mem_filter, Finset.mem_range] using hjmem
  have hright : s ≤ γ (F.sup id + 1) := by
    by_cases hlast : F.sup id + 1 = M
    · simpa only [hlast, hone] using hs.2
    · by_contra h
      have hnext : F.sup id + 1 ∈ F := by
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (by omega), (lt_of_not_ge h).le⟩
      have hle : F.sup id + 1 ≤ F.sup id := Finset.le_sup (f := id) hnext
      omega
  simpa only [roundIndex, hclamp, F] using ⟨hj.1, hj.2, hright⟩

/-- On a valid partition, the clamped weight equals the usual barycentric weight. -/
lemma roundWeight_eq_of_mem (K M : ℕ) (γ : ℕ → ℝ) (hΓ : IsGridPartition K M γ)
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    roundWeight M γ s =
      (s - γ (roundIndex M γ s)) /
        (γ (roundIndex M γ s + 1) - γ (roundIndex M γ s)) := by
  obtain ⟨hj, hlo, hhi⟩ := roundIndex_bounds K M γ hΓ s hs
  have hden : 0 < γ (roundIndex M γ s + 1) - γ (roundIndex M γ s) :=
    sub_pos.mpr (hΓ.2.2.1 _ hj)
  have hw0 : 0 ≤ (s - γ (roundIndex M γ s)) /
      (γ (roundIndex M γ s + 1) - γ (roundIndex M γ s)) :=
    div_nonneg (sub_nonneg.mpr hlo) hden.le
  have hw1 : (s - γ (roundIndex M γ s)) /
      (γ (roundIndex M γ s + 1) - γ (roundIndex M γ s)) ≤ 1 := by
    apply (div_le_one hden).2
    linarith
  simp only [roundWeight, clamp01_eq_of_mem hs, min_eq_right hw1, max_eq_right hw0]

/-- Integration against the two-point rounding law is a weighted endpoint average. -/
lemma integral_roundMeasure (M : ℕ) (γ : ℕ → ℝ) (s : ℝ) :
    ∫ p, p ∂(roundMeasure M γ s) =
      (1 - roundWeight M γ s) * γ (roundIndex M γ s) +
        roundWeight M γ s * γ (roundIndex M γ s + 1) := by
  have hw0 : 0 ≤ roundWeight M γ s := le_max_left _ _
  have hw1 : roundWeight M γ s ≤ 1 := by
    exact max_le (by norm_num) (min_le_left _ _)
  have ha : Integrable (fun p : ℝ => p)
      (ENNReal.ofReal (1 - roundWeight M γ s) • Measure.dirac (γ (roundIndex M γ s))) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  have hb : Integrable (fun p : ℝ => p)
      (ENNReal.ofReal (roundWeight M γ s) • Measure.dirac (γ (roundIndex M γ s + 1))) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  rw [roundMeasure, integral_add_measure ha hb]
  simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal hw0,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hw1), smul_eq_mul]

end CalibratedMA.Randomized

open CalibratedMA.Randomized

/-- Section 3.2, Eq. (4): the mission's exact pointwise mean-preservation target. -/
theorem solution (K M : ℕ) (γ : ℕ → ℝ) (hΓ : IsGridPartition K M γ) (s : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ∫ p, p ∂(roundMeasure M γ s) = s := by
  have hj := (roundIndex_bounds K M γ hΓ s hs).1
  have hden : γ (roundIndex M γ s + 1) - γ (roundIndex M γ s) ≠ 0 :=
    ne_of_gt (sub_pos.mpr (hΓ.2.2.1 _ hj))
  rw [integral_roundMeasure, roundWeight_eq_of_mem K M γ hΓ s hs]
  field_simp [hden]
  ring
