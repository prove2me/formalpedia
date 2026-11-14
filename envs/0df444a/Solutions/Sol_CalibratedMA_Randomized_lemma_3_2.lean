-- Prove2me | solution 1 for CalibratedMA.Randomized.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @Aaron
-- created : 2026-11-13T18:14:08.051258+00:00
-- url     : https://prove2.me/submissions/e29bab24-9b49-47c3-834b-959aa2d384a4

import Definitions.Def_CalibratedMA_Randomized_Rounding

open MeasureTheory

namespace CalibratedMA.Randomized.Interpolation

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

lemma grid_strictMonoOn (K M : ℕ) (γ : ℕ → ℝ) (hΓ : IsGridPartition K M γ) :
    StrictMonoOn γ (Set.Iic M) := by
  apply strictMonoOn_Iic_of_lt_succ
  intro j hj
  exact hΓ.2.2.1 j hj

noncomputable def affineValue (γ : ℕ → ℝ) (h : ℝ → ℝ) (j : ℕ) (s : ℝ) : ℝ :=
  h (γ j) * ((γ (j + 1) - s) / (γ (j + 1) - γ j)) +
    h (γ (j + 1)) * ((s - γ j) / (γ (j + 1) - γ j))

lemma affineValue_left (γ : ℕ → ℝ) (h : ℝ → ℝ) (j : ℕ)
    (hd : γ (j + 1) - γ j ≠ 0) : affineValue γ h j (γ j) = h (γ j) := by
  simp [affineValue, hd]

lemma affineValue_right (γ : ℕ → ℝ) (h : ℝ → ℝ) (j : ℕ)
    (hd : γ (j + 1) - γ j ≠ 0) : affineValue γ h j (γ (j + 1)) = h (γ (j + 1)) := by
  simp [affineValue, hd]

lemma integral_roundMeasure_test (M : ℕ) (γ : ℕ → ℝ) (s : ℝ) (h : ℝ → ℝ) :
    ∫ p, h p ∂(roundMeasure M γ s) =
      (1 - roundWeight M γ s) * h (γ (roundIndex M γ s)) +
        roundWeight M γ s * h (γ (roundIndex M γ s + 1)) := by
  have hw0 : 0 ≤ roundWeight M γ s := le_max_left _ _
  have hw1 : roundWeight M γ s ≤ 1 := max_le (by norm_num) (min_le_left _ _)
  have ha : Integrable h
      (ENNReal.ofReal (1 - roundWeight M γ s) • Measure.dirac (γ (roundIndex M γ s))) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  have hb : Integrable h
      (ENNReal.ofReal (roundWeight M γ s) • Measure.dirac (γ (roundIndex M γ s + 1))) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  rw [roundMeasure, integral_add_measure ha hb]
  simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal hw0,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hw1), smul_eq_mul]

lemma liftTest_selected (K M : ℕ) (γ : ℕ → ℝ) (hΓ : IsGridPartition K M γ)
    (h : ℝ → ℝ) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    liftTest M γ h s = affineValue γ h (roundIndex M γ s) s := by
  have hj := (roundIndex_bounds K M γ hΓ s hs).1
  have hd : γ (roundIndex M γ s + 1) - γ (roundIndex M γ s) ≠ 0 :=
    ne_of_gt (sub_pos.mpr (hΓ.2.2.1 _ hj))
  rw [liftTest, integral_roundMeasure_test, roundWeight_eq_of_mem K M γ hΓ s hs]
  unfold affineValue
  field_simp [hd]
  ring

lemma affineValue_eq_of_overlap (K M : ℕ) (γ : ℕ → ℝ) (hΓ : IsGridPartition K M γ)
    (h : ℝ → ℝ) (j k : ℕ) (hj : j < M) (hk : k < M) (s : ℝ)
    (hsj : s ∈ Set.Icc (γ j) (γ (j + 1)))
    (hsk : s ∈ Set.Icc (γ k) (γ (k + 1))) :
    affineValue γ h j s = affineValue γ h k s := by
  have hmono := (grid_strictMonoOn K M γ hΓ).monotoneOn
  have hdj : γ (j + 1) - γ j ≠ 0 := ne_of_gt (sub_pos.mpr (hΓ.2.2.1 _ hj))
  have hdk : γ (k + 1) - γ k ≠ 0 := ne_of_gt (sub_pos.mpr (hΓ.2.2.1 _ hk))
  rcases lt_trichotomy j k with hlt | rfl | hgt
  · have he : γ (j + 1) ≤ γ k := hmono (show j + 1 ≤ M by omega) (show k ≤ M by omega) (by omega)
    have hs1 : s = γ (j + 1) := by linarith [hsj.2, hsk.1]
    have hs2 : s = γ k := by linarith [hsj.2, hsk.1]
    calc
      affineValue γ h j s = h s := by rw [hs1, affineValue_right γ h j hdj]
      _ = affineValue γ h k s := by rw [hs2, affineValue_left γ h k hdk]
  · rfl
  · have he : γ (k + 1) ≤ γ j := hmono (show k + 1 ≤ M by omega) (show j ≤ M by omega) (by omega)
    have hs1 : s = γ j := by linarith [hsk.2, hsj.1]
    have hs2 : s = γ (k + 1) := by linarith [hsk.2, hsj.1]
    calc
      affineValue γ h j s = h s := by rw [hs1, affineValue_left γ h j hdj]
      _ = affineValue γ h k s := by rw [hs2, affineValue_right γ h k hdk]

lemma liftTest_formula (K M : ℕ) (γ : ℕ → ℝ) (hΓ : IsGridPartition K M γ)
    (h : ℝ → ℝ) :
    ∀ j < M, ∀ s ∈ Set.Icc (γ j) (γ (j + 1)),
      liftTest M γ h s =
        h (γ j) * ((γ (j + 1) - s) / (γ (j + 1) - γ j)) +
          h (γ (j + 1)) * ((s - γ j) / (γ (j + 1) - γ j)) := by
  intro j hj s hs
  have hmono := (grid_strictMonoOn K M γ hΓ).monotoneOn
  have hlo : 0 ≤ γ j := by simpa [hΓ.1] using hmono (Nat.zero_le M) (Nat.le_of_lt hj) (Nat.zero_le j)
  have hhi : γ (j + 1) ≤ 1 := by simpa [hΓ.2.1] using hmono (show j + 1 ≤ M by omega) (le_refl M) (show j + 1 ≤ M by omega)
  have hs01 : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hlo.trans hs.1, hs.2.trans hhi⟩
  obtain ⟨hk, hks⟩ := roundIndex_bounds K M γ hΓ s hs01
  rw [liftTest_selected K M γ hΓ h s hs01]
  exact affineValue_eq_of_overlap K M γ hΓ h _ j hk hj s hks hs

end CalibratedMA.Randomized.Interpolation



namespace CalibratedMA.Randomized.Interpolation

/-- A function that agrees with the affine interpolant on each closed partition interval
is continuous on the whole prediction interval. The closed intervals can be glued because
they are finitely many and the same function is used on their shared endpoints. -/
lemma continuousOn_of_interval_formula (K M : ℕ) (γ : ℕ → ℝ)
    (hΓ : IsGridPartition K M γ) (f h : ℝ → ℝ)
    (hformula : ∀ j < M, ∀ s ∈ Set.Icc (γ j) (γ (j + 1)),
      f s = h (γ j) * ((γ (j + 1) - s) / (γ (j + 1) - γ j)) +
        h (γ (j + 1)) * ((s - γ j) / (γ (j + 1) - γ j))) :
    ContinuousOn f (Set.Icc (0 : ℝ) 1) := by
  have hleft : ∀ j, j ≤ M → γ 0 ≤ γ j := by
    intro j
    induction j with
    | zero => intro _; exact le_rfl
    | succ j ih =>
      intro hj
      exact (ih (by omega)).trans (hΓ.2.2.1 j (by omega)).le
  have hsegment : ∀ j < M, ContinuousOn f (Set.Icc (γ j) (γ (j + 1))) := by
    intro j hj
    have haffine : Continuous (fun s : ℝ =>
        h (γ j) * ((γ (j + 1) - s) / (γ (j + 1) - γ j)) +
          h (γ (j + 1)) * ((s - γ j) / (γ (j + 1) - γ j))) := by
      fun_prop
    exact haffine.continuousOn.congr (fun s hs => hformula j hj s hs)
  have hpartial : ∀ j, j ≤ M → ContinuousOn f (Set.Icc (γ 0) (γ j)) := by
    intro j
    induction j with
    | zero =>
      intro _
      simpa only [Set.Icc_self] using continuousOn_singleton f (γ 0)
    | succ j ih =>
      intro hj
      have hjM : j < M := by omega
      have hu := (ih (by omega)).union_of_isClosed (hsegment j hjM)
        isClosed_Icc isClosed_Icc
      rw [Set.Icc_union_Icc_eq_Icc (hleft j (by omega)) (hΓ.2.2.1 j hjM).le] at hu
      exact hu
  simpa only [hΓ.1, hΓ.2.1] using hpartial M le_rfl

end CalibratedMA.Randomized.Interpolation

open CalibratedMA.Randomized

/-- Lemma 3.2 (p. 14): the lift `a_h(s) = E[h(Round_Γ(s))]` of a test `h` on the partition
points is the linear interpolation of the values `h(γ_j)` on each interval `[γ_j, γ_{j+1}]`,
and it is continuous on `[0,1]`. -/
theorem solution (K M : ℕ) (γ : ℕ → ℝ) (hΓ : IsGridPartition K M γ) (h : ℝ → ℝ) :
    (∀ j < M, ∀ s ∈ Set.Icc (γ j) (γ (j + 1)),
      liftTest M γ h s =
        h (γ j) * ((γ (j + 1) - s) / (γ (j + 1) - γ j)) +
          h (γ (j + 1)) * ((s - γ j) / (γ (j + 1) - γ j))) ∧
    ContinuousOn (liftTest M γ h) (Set.Icc (0 : ℝ) 1) := by
  have hf := Interpolation.liftTest_formula K M γ hΓ h
  exact ⟨hf, Interpolation.continuousOn_of_interval_formula K M γ hΓ (liftTest M γ h) h hf⟩

