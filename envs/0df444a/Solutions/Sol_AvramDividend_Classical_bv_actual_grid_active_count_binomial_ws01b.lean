-- Prove2me | solution 1 for AvramDividend.Classical.bv_actual_grid_active_count_binomial_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:18:57.122172+00:00
-- url     : https://prove2.me/submissions/7d6f858e-9673-435c-b3a2-f32120551830

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_grid_binary_coverage_ae
import Theorems.Thm_AvramDividend_Classical_bv_binary_grid_count_partition_ws01b
import Theorems.Thm_AvramDividend_Classical_bv_actual_grid_binomial_complete_pattern_mass_ws01b
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal BigOperators
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (t : ℕ → ℝ≥0) (ht : Monotone t)
    (n k : ℕ) (h : ℝ)
    (hgap : ∀ i : ℕ, i < n →
      (((t (i + 1) - t i : ℝ≥0) : ℝ)) = h) :
    P.real {ω : Ω |
      ((Finset.range n).filter (fun i =>
        X.X (t (i + 1)) ω - X.X (t i) ω <
          X.drift * (((t (i + 1) - t i : ℝ≥0) : ℝ)))).card = k} =
      (Nat.choose n k : ℝ) *
        (1 - Real.exp (-(h * (X.ν (Iio (0 : ℝ))).toReal))) ^ k *
        (Real.exp (-(h * (X.ν (Iio (0 : ℝ))).toReal))) ^ (n - k) := by
  let A : ℕ → Set Ω := fun i => {ω |
    X.X (t (i + 1)) ω - X.X (t i) ω <
      X.drift * (((t (i + 1) - t i : ℝ≥0) : ℝ))}
  let B : ℕ → Set Ω := fun i => {ω |
    X.X (t (i + 1)) ω - X.X (t i) ω =
      X.drift * (((t (i + 1) - t i : ℝ≥0) : ℝ))}
  have hExcl : ∀ i : ℕ, i < n → ∀ ω : Ω, ω ∈ A i → ω ∈ B i → False := by
    intro i hi ω ha hb
    change X.X (t (i + 1)) ω - X.X (t i) ω <
      X.drift * (((t (i + 1) - t i : ℝ≥0) : ℝ)) at ha
    change X.X (t (i + 1)) ω - X.X (t i) ω =
      X.drift * (((t (i + 1) - t i : ℝ≥0) : ℝ)) at hb
    linarith
  have hCover : ∀ᵐ ω ∂P, ∀ i : ℕ, i < n → ω ∈ A i ∨ ω ∈ B i := by
    filter_upwards [avram_wave4_04a_bv_actual_grid_binary_coverage_ae X hBV t ht n]
      with ω hw
    intro i hi
    rcases hw i hi with hlt | heq
    · exact Or.inl (by simpa [A] using hlt)
    · exact Or.inr (by simpa [B] using heq)
  calc
    P.real {ω : Ω | ((Finset.range n).filter (fun i =>
      X.X (t (i + 1)) ω - X.X (t i) ω <
        X.drift * (((t (i + 1) - t i : ℝ≥0) : ℝ)))).card = k} =
      P.real {ω : Ω | (∀ i : ℕ, i < n → ω ∈ A i ∨ ω ∈ B i) ∧
        ((Finset.range n).filter (fun i => ω ∈ A i)).card = k} := by
      apply congrArg ENNReal.toReal
      apply measure_congr
      filter_upwards [hCover] with ω hω
      exact propext ⟨fun hk => ⟨hω, hk⟩, fun hk => hk.2⟩
    _ = P.real {ω : Ω | ∃ S ∈ Finset.powersetCard k (Finset.range n),
        ∀ i : ℕ, i < n → if i ∈ S then ω ∈ A i else ω ∈ B i} := by
      rw [bv_binary_grid_count_partition_ws01b A B n k hExcl]
    _ = (Nat.choose n k : ℝ) *
        (1 - Real.exp (-(h * (X.ν (Iio (0 : ℝ))).toReal))) ^ k *
        (Real.exp (-(h * (X.ν (Iio (0 : ℝ))).toReal))) ^ (n - k) := by
      convert bv_actual_grid_binomial_complete_pattern_mass_ws01b
        X hBV hFinite t ht n k h hgap using 1
      congr 1
      ext ω
      apply exists_congr
      intro S
      apply and_congr_right
      intro _
      apply forall_congr'
      intro i
      apply imp_congr_right
      intro _
      by_cases his : i ∈ S
      · simp [his, A]
      · simp [his, B]
