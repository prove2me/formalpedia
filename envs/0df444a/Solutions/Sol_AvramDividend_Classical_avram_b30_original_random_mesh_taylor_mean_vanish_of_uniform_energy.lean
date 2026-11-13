-- Prove2me | solution 1 for AvramDividend.Classical.avram_b30_original_random_mesh_taylor_mean_vanish_of_uniform_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T00:12:16.746688+00:00
-- url     : https://prove2.me/submissions/87958e39-01b1-4c27-8a9b-441c71136b9d

import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b28_original_random_clipped_C2_taylor_L1_automatic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Metric Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Uniform original-source quadratic energy and shrinking stopped cells force true C2 Taylor L1 errors to vanish. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbcap : ENNReal.ofReal b < C) :
    ∀ (A : Set Ω) (S : ℕ → Finset ℕ)
      (s t : ℕ → ℕ → Ω → ℝ≥0),
      let z : ℕ → Ω → ℕ → ℝ := fun m ω i =>
        Function.leftLim (fun u : ℝ≥0 =>
          x + X.X u ω - rightLimit D u ω) (s m i ω)
      let g : ℕ → Ω → ℕ → ℝ := fun m ω i =>
        X.X (t m i ω) ω - X.X (s m i ω) ω -
          ((t m i ω - s m i ω) : ℝ) * X.c
      let Q : ℕ → Ω → ℝ := fun m ω =>
        ∑ i ∈ S m, (g m ω i) ^ 2
      let R : ℕ → Ω → ℝ := fun m ω => ∑ i ∈ S m,
        (w (z m ω i + g m ω i) -
          taylorWithinEval w 1
            (Set.uIcc (z m ω i) (z m ω i + g m ω i))
            (z m ω i) (z m ω i + g m ω i) -
          (iteratedDeriv 2 w (z m ω i) * (g m ω i) ^ 2) / 2)
      (∀ m i, i ∈ S m → IsStoppingTime 𝓕.rightCont
        (fun ω => (s m i ω : WithTop ℝ≥0))) →
      (∀ m i, i ∈ S m → IsStoppingTime 𝓕.rightCont
        (fun ω => (t m i ω : WithTop ℝ≥0))) →
      (∀ m, ∀ᵐ ω ∂(P.restrict A), ∀ i ∈ S m,
        z m ω i ∈ Icc a b ∧ z m ω i + g m ω i ∈ Icc a b ∧
        z m ω i ≠ z m ω i + g m ω i) →
      (∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ m, N ≤ m →
        ∀ᵐ ω ∂(P.restrict A), ∀ i ∈ S m,
          dist (z m ω i + g m ω i) (z m ω i) < δ) →
      (∀ m, AEStronglyMeasurable (fun ω => |R m ω|) (P.restrict A)) →
      (∃ K : ℝ, 0 ≤ K ∧ ∀ m, (∫ ω in A, Q m ω ∂P) ≤ K) →
      Tendsto (fun m => ∫ ω in A, |R m ω| ∂P)
        atTop (𝓝 (0 : ℝ)) := by
  classical
  intro A S s t
  dsimp only
  intro hs ht hBand hSmall hRMeas hQBound
  let z : ℕ → Ω → ℕ → ℝ := fun m ω i =>
    Function.leftLim (fun u : ℝ≥0 =>
      x + X.X u ω - rightLimit D u ω) (s m i ω)
  let g : ℕ → Ω → ℕ → ℝ := fun m ω i =>
    X.X (t m i ω) ω - X.X (s m i ω) ω -
      ((t m i ω - s m i ω) : ℝ) * X.c
  let Q : ℕ → Ω → ℝ := fun m ω =>
    ∑ i ∈ S m, (g m ω i) ^ 2
  let R : ℕ → Ω → ℝ := fun m ω => ∑ i ∈ S m,
    (w (z m ω i + g m ω i) -
      taylorWithinEval w 1
        (Set.uIcc (z m ω i) (z m ω i + g m ω i))
        (z m ω i) (z m ω i + g m ω i) -
      (iteratedDeriv 2 w (z m ω i) * (g m ω i) ^ 2) / 2)
  obtain ⟨K, hK, hQ⟩ := hQBound
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hKpos : 0 < K + 1 := by linarith
  have hεfrac : 0 < ε / (K + 1) := div_pos hε hKpos
  obtain ⟨δ, hδ, hTaylor⟩ :=
    avram_b28_original_random_clipped_C2_taylor_L1_automatic
      X x D hD C w hw a b ha hab hbcap
      (ε / (K + 1)) hεfrac
  obtain ⟨N, hN⟩ := hSmall δ hδ
  refine ⟨N, ?_⟩
  intro m hm
  have hBandSmall : ∀ᵐ ω ∂(P.restrict A), ∀ i ∈ S m,
      z m ω i ∈ Icc a b ∧
      z m ω i + g m ω i ∈ Icc a b ∧
      z m ω i ≠ z m ω i + g m ω i ∧
      dist (z m ω i + g m ω i) (z m ω i) < δ := by
    filter_upwards [hBand m, hN m hm] with ω hB hS i hi
    exact ⟨(hB i hi).1, (hB i hi).2.1,
      (hB i hi).2.2, hS i hi⟩
  have hT :=
    (hTaylor A (S m) (s m) (t m)
      (fun i hi => hs m i hi)
      (fun i hi => ht m i hi)
      hBandSmall (hRMeas m)).2
  have hBound : (∫ ω in A, |R m ω| ∂P) ≤
      (ε / (K + 1)) * (∫ ω in A, Q m ω ∂P) := hT
  have hRnonneg : 0 ≤ (∫ ω in A, |R m ω| ∂P) :=
    integral_nonneg (fun ω => abs_nonneg _)
  have hKfrac : K / (K + 1) < 1 :=
    (div_lt_iff₀ hKpos).2 (by linarith)
  have hLimit : (ε / (K + 1)) * K < ε := by
    calc
      (ε / (K + 1)) * K = ε * (K / (K + 1)) := by ring
      _ < ε := by
        simpa only [mul_one] using mul_lt_mul_of_pos_left hKfrac hε
  have hSmallMean : (∫ ω in A, |R m ω| ∂P) < ε :=
    lt_of_le_of_lt
      (hBound.trans (mul_le_mul_of_nonneg_left (hQ m) (le_of_lt hεfrac)))
      hLimit
  change dist (∫ ω in A, |R m ω| ∂P) 0 < ε
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hRnonneg] using hSmallMean
