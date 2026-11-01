-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_sourceLevy_closedHorizon_fullStieltjes_exponential_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T20:19:15.689575+00:00
-- url     : https://prove2.me/submissions/529c4c4a-9f26-4a87-8f9d-3f696b672010

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_original_source_fullStieltjes_doubleFatou_expected
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_rightDyadic_allRealIoc_step_eq_ceiling
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_zeroAtom_plus_fullStieltjes_doubleLintegral_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Genuine closed-horizon expected source Lévy exponential cash budget,
including the time-zero atom and all positive-time Stieltjes mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ≥0) (hT : 0 < T) :
    (∫⁻ ω, ENNReal.ofReal (1 * Real.exp (-(1 * rightLimit D 0 ω)) *
      rightLimit D 0 ω) ∂P) +
    (∫⁻ ω, ∫⁻ s : ℝ, if s ∈ Ioc (0 : ℝ) (T : ℝ) then
      ENNReal.ofReal (Real.exp (X.X s.toNNReal ω -
        rightLimit D s.toNNReal ω - (s.toNNReal : ℝ) * X.ψ 1))
      else 0 ∂dividendMeasure D ω ∂P) ≤ 1 := by
  classical
  let A : ℝ≥0∞ :=
    ∫⁻ ω, ENNReal.ofReal (1 * Real.exp (-(1 * rightLimit D 0 ω)) *
      rightLimit D 0 ω) ∂P
  let S : ℕ → ℝ≥0∞ := fun n =>
    ∫⁻ ω, ∫⁻ s : ℝ,
      if s ∈ Ioc (0 : ℝ) (T : ℝ) then
        let k := Nat.ceil (((s.toNNReal / T : ℝ≥0) : ℝ) * (2 : ℝ) ^ n)
        let u := ((k : ℝ≥0) / (2 : ℝ≥0) ^ n) * T
        ENNReal.ofReal (Real.exp
          (X.X u ω - rightLimit D u ω - (u : ℝ) * X.ψ 1))
      else 0 ∂dividendMeasure D ω ∂P
  have hfatou :
      (∫⁻ ω, ∫⁻ s : ℝ, if s ∈ Ioc (0 : ℝ) (T : ℝ) then
        ENNReal.ofReal (Real.exp (X.X s.toNNReal ω -
          rightLimit D s.toNNReal ω - (s.toNNReal : ℝ) * X.ψ 1))
        else 0 ∂dividendMeasure D ω ∂P) ≤
      Filter.liminf S atTop := by
    simpa only [S, zero_add, one_mul] using
      (avram_wave4_03_original_source_fullStieltjes_doubleFatou_expected
        X 0 D hD 1 (X.ψ 1) T hT)
  have hfactor (t : ℝ≥0) (ω : Ω) :
      ENNReal.ofReal (Real.exp
        (X.X t ω - rightLimit D t ω - (t : ℝ) * X.ψ 1)) =
      ENNReal.ofReal (1 *
        Real.exp (X.X t ω - (t : ℝ) * X.ψ 1) *
        Real.exp (-(1 * rightLimit D t ω))) := by
    congr 1
    rw [show X.X t ω - rightLimit D t ω - (t : ℝ) * X.ψ 1 =
      (X.X t ω - (t : ℝ) * X.ψ 1) + (-rightLimit D t ω) by ring,
      Real.exp_add]
    ring
  have hbound (n : ℕ) : A + S n ≤ 1 := by
    let u : ℕ → ℝ≥0 :=
      fun i => ((i : ℝ≥0) / (2 : ℝ≥0) ^ n) * T
    have hu : Monotone u := by
      intro i j hij
      dsimp [u]
      gcongr
    have hu0 : u 0 = 0 := by simp [u]
    have hbudget :=
      avram_wave4_03_sourceLevy_zeroAtom_plus_fullStieltjes_doubleLintegral_budget
        X D hD 1 (by norm_num) u hu hu0 (2 ^ n)
    have hstep :
        S n =
        (∫⁻ ω, ∫⁻ s : ℝ,
          ∑ i ∈ Finset.range (2 ^ n),
            if s ∈ Ioc (u i : ℝ) (u (i + 1) : ℝ) then
              ENNReal.ofReal (Real.exp
                (X.X (u (i + 1)) ω -
                  rightLimit D (u (i + 1)) ω -
                  (u (i + 1) : ℝ) * X.ψ 1))
            else 0 ∂dividendMeasure D ω ∂P) := by
      dsimp [S]
      apply lintegral_congr_ae
      filter_upwards [] with ω
      apply lintegral_congr_ae
      filter_upwards [] with s
      let a : ℕ → ℝ≥0∞ := fun k =>
        ENNReal.ofReal (Real.exp
          (X.X (((k : ℝ≥0) / (2 : ℝ≥0) ^ n) * T) ω -
            rightLimit D (((k : ℝ≥0) / (2 : ℝ≥0) ^ n) * T) ω -
            ((((k : ℝ≥0) / (2 : ℝ≥0) ^ n) * T) : ℝ) * X.ψ 1))
      exact (avram_wave4_03_rightDyadic_allRealIoc_step_eq_ceiling
        T hT s n a).symm
    rw [hstep]
    have hcell :
        (∫⁻ ω, ∫⁻ s : ℝ,
          ∑ i ∈ Finset.range (2 ^ n),
            if s ∈ Ioc (u i : ℝ) (u (i + 1) : ℝ) then
              ENNReal.ofReal (Real.exp
                (X.X (u (i + 1)) ω -
                  rightLimit D (u (i + 1)) ω -
                  (u (i + 1) : ℝ) * X.ψ 1))
            else 0 ∂dividendMeasure D ω ∂P) =
        (∫⁻ ω, ∫⁻ s : ℝ,
          ∑ i ∈ Finset.range (2 ^ n),
            if s ∈ Ioc (u i : ℝ) (u (i + 1) : ℝ) then
              ENNReal.ofReal (1 *
                Real.exp (X.X (u (i + 1)) ω -
                  (u (i + 1) : ℝ) * X.ψ 1) *
                Real.exp (-(1 * rightLimit D (u (i + 1)) ω)))
            else 0 ∂dividendMeasure D ω ∂P) := by
      apply lintegral_congr_ae
      filter_upwards [] with ω
      apply lintegral_congr_ae
      filter_upwards [] with s
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hs : s ∈ Ioc (u i : ℝ) (u (i + 1) : ℝ)
      · simpa only [if_pos hs] using hfactor (u (i + 1)) ω
      · simp only [if_neg hs]
    rw [hcell]
    simpa only [A, one_mul] using hbudget
  have hA_le : A ≤ 1 := by
    calc
      A ≤ A + S 0 := le_add_of_nonneg_right (by positivity)
      _ ≤ 1 := hbound 0
  have hA_ne : A ≠ ⊤ :=
    (lt_of_le_of_lt hA_le ENNReal.one_lt_top).ne
  have hS_le (n : ℕ) : S n ≤ 1 - A :=
    ENNReal.le_sub_of_add_le_left hA_ne (hbound n)
  have hlim : Filter.liminf S atTop ≤ 1 - A := by
    calc
      _ ≤ Filter.liminf (fun _ : ℕ => 1 - A) atTop :=
        Filter.liminf_le_liminf (Filter.Eventually.of_forall hS_le)
      _ = 1 - A := by simp
  have hfinal : A + (∫⁻ ω, ∫⁻ s : ℝ, if s ∈ Ioc (0 : ℝ) (T : ℝ) then
      ENNReal.ofReal (Real.exp (X.X s.toNNReal ω -
        rightLimit D s.toNNReal ω - (s.toNNReal : ℝ) * X.ψ 1))
      else 0 ∂dividendMeasure D ω ∂P) ≤ 1 := by
    calc
      _ ≤ A + Filter.liminf S atTop := add_le_add_right hfatou A
      _ ≤ A + (1 - A) := add_le_add_right hlim A
      _ = 1 := add_tsub_cancel_of_le hA_le
  simpa only [A] using hfinal
