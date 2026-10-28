-- Prove2me | solution 1 for AvramDividend.Classical.chat04_terminal_restricted_fixed_horizon_strict_reversal_ws01a
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T12:38:12.145034+00:00
-- url     : https://prove2.me/submissions/6543d565-dd53-4f94-a855-9b91df4d8ea9

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_right_continuous_strict_dyadic_grid_event
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_finite_dyadic_grid_refines
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_strict_grid_path_probability_of_vector_reversal
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_levy_increment_vector_tilted_reversal
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_map_withDensity_observable_density
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_fin_mesh_increment_sum_terminal
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_fin_reverse_preserves_sum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology Finset Set
open scoped NNReal ENNReal BigOperators

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (hT : 0 < T)
    (a c : ℝ) :
    (P.withDensity (fun ω : Ω =>
      if X.X T ω - X.X 0 ω < c then (1 : ℝ≥0∞) else 0))
      {ω : Ω | ∃ s : ℝ≥0, s ≤ T ∧ X.X T ω - X.X s ω < a} =
    (P.withDensity (fun ω : Ω =>
      if X.X T ω - X.X 0 ω < c then (1 : ℝ≥0∞) else 0))
      {ω : Ω | ∃ s : ℝ≥0, s ≤ T ∧ X.X s ω - X.X 0 ω < a} := by
  let Q : Measure Ω := P.withDensity (fun ω : Ω =>
    if X.X T ω - X.X 0 ω < c then (1 : ℝ≥0∞) else 0)
  let G : ℕ → (ℝ≥0 → ℝ) → Prop := fun n f =>
    ∃ k : Fin ((2 : ℕ) ^ n + 1),
      f (((k.val : ℝ≥0) / (2 : ℝ≥0) ^ n) * T) < a
  have hmono : ∀ f : ℝ≥0 → ℝ, Monotone (fun n => G n f) := by
    intro f
    refine monotone_nat_of_le_succ (fun n => ?_)
    rintro ⟨k, hk⟩
    obtain ⟨j, hj⟩ := avram_ws01e_b_finite_dyadic_grid_refines T n k
    exact ⟨j, by simpa only [hj] using hk⟩
  have hA : {ω : Ω | ∃ s : ℝ≥0, s ≤ T ∧ X.X T ω - X.X s ω < a} =
      ⋃ n, {ω | G n (fun s => X.X T ω - X.X s ω)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    refine avram_ws01e_b_right_continuous_strict_dyadic_grid_event
      (fun s => X.X T ω - X.X s ω) T hT (fun s => ?_) a
    exact continuousWithinAt_const.sub (X.rightCont ω s)
  have hB : {ω : Ω | ∃ s : ℝ≥0, s ≤ T ∧ X.X s ω - X.X 0 ω < a} =
      ⋃ n, {ω | G n (fun s => X.X s ω - X.X 0 ω)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    refine avram_ws01e_b_right_continuous_strict_dyadic_grid_event
      (fun s => X.X s ω - X.X 0 ω) T hT (fun s => ?_) a
    exact (X.rightCont ω s).sub continuousWithinAt_const
  have hgrid : ∀ n (k : ℕ),
      ((k : ℝ≥0) / (2 : ℝ≥0) ^ n) * T =
      (k : ℝ≥0) * (T / 2 ^ n) := by
    intro n k
    rw [div_mul_eq_mul_div, mul_div_assoc]
  have heq : ∀ n, Q {ω | G n (fun s => X.X T ω - X.X s ω)} =
      Q {ω | G n (fun s => X.X s ω - X.X 0 ω)} := by
    intro n
    have hT' : (((2 ^ n : ℕ) : ℝ≥0)) * (T / 2 ^ n) = T := by
      push_cast
      rw [mul_div_cancel₀]
      positivity
    let F : Ω → (Fin (2 ^ n) → ℝ) := fun ω i =>
      X.X (((i.val + 1 : ℕ) : ℝ≥0) * (T / 2 ^ n)) ω -
        X.X ((i.val : ℝ≥0) * (T / 2 ^ n)) ω
    let R : (Fin (2 ^ n) → ℝ) → (Fin (2 ^ n) → ℝ) :=
      fun v i => v i.rev
    let ρ : (Fin (2 ^ n) → ℝ) → ℝ≥0∞ := fun v =>
      if (∑ i : Fin (2 ^ n), v i) < c then 1 else 0
    have hF : Measurable F := by
      apply measurable_pi_lambda
      intro i
      exact (X.adapted.measurable).sub (X.adapted.measurable)
    have hR : Measurable R := by
      apply measurable_pi_lambda
      intro i
      exact measurable_pi_apply i.rev
    have hSum : Measurable (fun v : Fin (2 ^ n) → ℝ =>
        ∑ i : Fin (2 ^ n), v i) :=
      Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)
    have hρ : Measurable ρ := by
      classical
      change Measurable (fun v : Fin (2 ^ n) → ℝ =>
        if v ∈ (fun z : Fin (2 ^ n) → ℝ =>
          ∑ i : Fin (2 ^ n), z i) ⁻¹' Iio c
        then (1 : ℝ≥0∞) else 0)
      exact Measurable.ite (measurableSet_Iio.preimage hSum)
        measurable_const measurable_const
    have hρR : ∀ v : Fin (2 ^ n) → ℝ, ρ (R v) = ρ v := by
      intro v
      simp only [ρ, R, avram_ws01e_b_fin_reverse_preserves_sum]
    have hDensity : ∀ ω : Ω, ρ (F ω) =
        (if X.X T ω - X.X 0 ω < c then (1 : ℝ≥0∞) else 0) := by
      intro ω
      dsimp [ρ, F]
      rw [avram_ws01e_b_fin_mesh_increment_sum_terminal
        X (T / 2 ^ n) (2 ^ n) ω, hT']
    have hQ : Q = P.withDensity (ρ ∘ F) := by
      dsimp [Q]
      congr 1
      funext ω
      exact (hDensity ω).symm
    have hReversal : ∀ A : Set (Fin (2 ^ n) → ℝ), MeasurableSet A →
      Q {ω : Ω | (fun i : Fin (2 ^ n) =>
          X.X (((i.rev.val + 1 : ℕ) : ℝ≥0) * (T / 2 ^ n)) ω -
          X.X ((i.rev.val : ℝ≥0) * (T / 2 ^ n)) ω) ∈ A} =
      Q {ω : Ω | (fun i : Fin (2 ^ n) =>
          X.X (((i.val + 1 : ℕ) : ℝ≥0) * (T / 2 ^ n)) ω -
          X.X ((i.val : ℝ≥0) * (T / 2 ^ n)) ω) ∈ A} := by
      intro A hA
      have hTilt := avram_ws01e_b_levy_increment_vector_tilted_reversal
        X (T / 2 ^ n) (2 ^ n) ρ hρ hρR A hA
      change ((Measure.map F P).withDensity ρ) (R ⁻¹' A) =
        ((Measure.map F P).withDensity ρ) A at hTilt
      have hPush := avram_ws01e_b_map_withDensity_observable_density
        P F hF ρ hρ
      rw [← hPush, Measure.map_apply hF (hA.preimage hR),
        Measure.map_apply hF hA] at hTilt
      rw [← hQ] at hTilt
      simpa only [F, R, Set.preimage, Set.mem_setOf_eq,
        Function.comp_def] using hTilt
    have h := avram_ws01e_b_strict_grid_path_probability_of_vector_reversal
      X (T / 2 ^ n) (2 ^ n) Q a hReversal
    simp only [G, hgrid]
    rw [hT'] at h
    convert h using 3
  have m1 : Monotone (fun n =>
      {ω | G n (fun s => X.X T ω - X.X s ω)}) :=
    fun m n hmn ω h =>
      hmono (fun s => X.X T ω - X.X s ω) hmn h
  have m2 : Monotone (fun n =>
      {ω | G n (fun s => X.X s ω - X.X 0 ω)}) :=
    fun m n hmn ω h =>
      hmono (fun s => X.X s ω - X.X 0 ω) hmn h
  change Q {ω : Ω | ∃ s : ℝ≥0, s ≤ T ∧
      X.X T ω - X.X s ω < a} =
    Q {ω : Ω | ∃ s : ℝ≥0, s ≤ T ∧
      X.X s ω - X.X 0 ω < a}
  rw [hA, hB, m1.measure_iUnion, m2.measure_iUnion]
  simp_rw [heq]
