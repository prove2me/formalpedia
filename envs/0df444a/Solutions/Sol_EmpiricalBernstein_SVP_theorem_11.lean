-- Prove2me | solution 1 for EmpiricalBernstein.SVP.theorem_11
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T22:02:36.358508+00:00
-- url     : https://prove2.me/submissions/6d13bf70-ca5d-4820-9b2f-299e82c0b8a2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_EmpiricalBernstein_SVP_bennett_independent
import Theorems.Thm_EmpiricalBernstein_SVP_theorem_10
import Theorems.Thm_EmpiricalBernstein_SVP_eq_7_9

open MeasureTheory ProbabilityTheory VarianceRegularization.Expansion EmpiricalBernstein.SVP

private lemma sampleVar_nonneg {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) :
    0 ≤ sampleVar x := by
  unfold sampleVar
  have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  apply mul_nonneg
  · apply inv_nonneg.mpr
    nlinarith
  · positivity

private lemma empirical_bernstein_algebra {N V E W L : ℝ} (hN : 2 ≤ N)
    (hV : 0 ≤ V) (hL : 0 ≤ L) (hWE : W ≤ E)
    (hE : Real.sqrt E ≤ Real.sqrt V + Real.sqrt (2 * L / (N - 1))) :
    Real.sqrt (2 * W * L / N) + L / (3 * N) ≤
      Real.sqrt (2 * V * L / N) + 7 * L / (3 * (N - 1)) := by
  have hN0 : 0 < N := by linarith
  have hNm1 : 0 < N - 1 := by linarith
  have hWsqrt : Real.sqrt (2 * W * L / N) ≤
      Real.sqrt (2 * L / N) * Real.sqrt E := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ 2 * L / N)]
    apply Real.sqrt_le_sqrt
    calc
      2 * W * L / N = (2 * L / N) * W := by ring
      _ ≤ (2 * L / N) * E := mul_le_mul_of_nonneg_left hWE (by positivity)
      _ = (2 * L / N) * E := by ring
  have hspread := mul_le_mul_of_nonneg_left hE (Real.sqrt_nonneg (2 * L / N))
  have hmain : Real.sqrt (2 * W * L / N) ≤
      Real.sqrt (2 * L / N) * Real.sqrt V +
        Real.sqrt (2 * L / N) * Real.sqrt (2 * L / (N - 1)) := by
    calc
      Real.sqrt (2 * W * L / N) ≤ Real.sqrt (2 * L / N) * Real.sqrt E := hWsqrt
      _ ≤ Real.sqrt (2 * L / N) *
          (Real.sqrt V + Real.sqrt (2 * L / (N - 1))) := hspread
      _ = _ := by ring
  have hfirst : Real.sqrt (2 * L / N) * Real.sqrt V =
      Real.sqrt (2 * V * L / N) := by
    rw [mul_comm, ← Real.sqrt_mul hV]
    congr 1
    ring
  rw [hfirst] at hmain
  have hfrac : 2 * L / N ≤ 2 * L / (N - 1) := by
    rw [div_le_div_iff₀ hN0 hNm1]
    nlinarith
  have hsecond : Real.sqrt (2 * L / N) * Real.sqrt (2 * L / (N - 1)) ≤
      2 * L / (N - 1) := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ 2 * L / N), Real.sqrt_le_iff]
    constructor
    · positivity
    · calc
        (2 * L / N) * (2 * L / (N - 1)) ≤
            (2 * L / (N - 1)) * (2 * L / (N - 1)) :=
          mul_le_mul_of_nonneg_right hfrac (by positivity)
        _ = (2 * L / (N - 1)) ^ 2 := by ring
  have hlin : L / (3 * N) ≤ L / (3 * (N - 1)) := by
    rw [div_le_div_iff₀ (by positivity : 0 < 3 * N) (by positivity : 0 < 3 * (N - 1))]
    nlinarith
  calc
    Real.sqrt (2 * W * L / N) + L / (3 * N) ≤
        (Real.sqrt (2 * V * L / N) +
          Real.sqrt (2 * L / N) * Real.sqrt (2 * L / (N - 1))) + L / (3 * N) :=
      add_le_add_left hmain _
    _ ≤ (Real.sqrt (2 * V * L / N) + 2 * L / (N - 1)) + L / (3 * (N - 1)) := by
      linarith
    _ = Real.sqrt (2 * V * L / N) + 7 * L / (3 * (N - 1)) := by
      field_simp
      ring

theorem solution {n : ℕ} (hn : 2 ≤ n) (μs : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μs i)] (hμs : ∀ i, μs i (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (δ : ℝ) (hδ : 0 < δ) :
    Measure.pi μs {x | (∫ z, empMean z ∂(Measure.pi μs))
        > empMean x + Real.sqrt (2 * sampleVar x * Real.log (2 / δ) / n)
          + 7 * Real.log (2 / δ) / (3 * ((n : ℝ) - 1))}
      ≤ ENNReal.ofReal δ := by
  by_cases hδ2 : 2 < δ
  · calc
      Measure.pi μs {x | (∫ z, empMean z ∂(Measure.pi μs))
          > empMean x + Real.sqrt (2 * sampleVar x * Real.log (2 / δ) / n)
            + 7 * Real.log (2 / δ) / (3 * ((n : ℝ) - 1))}
          ≤ Measure.pi μs Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
      _ = ENNReal.ofReal 1 := by simp
      _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal (by linarith)
  · have hδle : δ ≤ 2 := le_of_not_gt hδ2
    have hδhalf : 0 < δ / 2 := by linarith
    have hdelta : 1 / (δ / 2) = 2 / δ := by field_simp
    have hL : 0 ≤ Real.log (2 / δ) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ hδ]
      linarith
    let B : Set (Fin n → ℝ) := {x | (∫ z, empMean z ∂(Measure.pi μs))
      > empMean x + Real.sqrt (2 * ((1 / (n : ℝ)) *
          ∑ i, variance (fun y : ℝ => y) (μs i)) * Real.log (2 / δ) / n)
        + Real.log (2 / δ) / (3 * n)}
    let C : Set (Fin n → ℝ) := {x |
      Real.sqrt (∫ z, sampleVar z ∂(Measure.pi μs)) >
        Real.sqrt (sampleVar x) + Real.sqrt (2 * Real.log (2 / δ) / ((n : ℝ) - 1))}
    have hB : Measure.pi μs B ≤ ENNReal.ofReal (δ / 2) := by
      simpa [B, hdelta] using
        (bennett_independent (by omega : 1 ≤ n) μs hμs (δ / 2) hδhalf)
    have hC : Measure.pi μs C ≤ ENNReal.ofReal (δ / 2) := by
      simpa [C, hdelta] using (theorem_10 hn μs hμs (δ / 2) hδhalf).1
    have hW : (1 / (n : ℝ)) * ∑ i, variance (fun y : ℝ => y) (μs i) ≤
        ∫ z, sampleVar z ∂(Measure.pi μs) := (eq_7_9 hn μs hμs).1
    have hsub : {x | (∫ z, empMean z ∂(Measure.pi μs))
        > empMean x + Real.sqrt (2 * sampleVar x * Real.log (2 / δ) / n)
          + 7 * Real.log (2 / δ) / (3 * ((n : ℝ) - 1))} ⊆ B ∪ C := by
      intro x hx
      by_contra hxc
      have hxB : x ∉ B := fun h => hxc (Or.inl h)
      have hxC : x ∉ C := fun h => hxc (Or.inr h)
      have hnotB : (∫ z, empMean z ∂(Measure.pi μs)) ≤
          empMean x + Real.sqrt (2 * ((1 / (n : ℝ)) *
            ∑ i, variance (fun y : ℝ => y) (μs i)) * Real.log (2 / δ) / n)
            + Real.log (2 / δ) / (3 * n) := by
        exact le_of_not_gt (by simpa [B] using hxB)
      have hnotC : Real.sqrt (∫ z, sampleVar z ∂(Measure.pi μs)) ≤
          Real.sqrt (sampleVar x) + Real.sqrt (2 * Real.log (2 / δ) / ((n : ℝ) - 1)) := by
        exact le_of_not_gt (by simpa [C] using hxC)
      have harith := empirical_bernstein_algebra
        (N := (n : ℝ)) (V := sampleVar x)
        (E := ∫ z, sampleVar z ∂(Measure.pi μs))
        (W := (1 / (n : ℝ)) * ∑ i, variance (fun y : ℝ => y) (μs i))
        (L := Real.log (2 / δ)) (by exact_mod_cast hn)
        (sampleVar_nonneg hn x) hL hW hnotC
      change (∫ z, empMean z ∂(Measure.pi μs)) >
        empMean x + Real.sqrt (2 * sampleVar x * Real.log (2 / δ) / n)
          + 7 * Real.log (2 / δ) / (3 * ((n : ℝ) - 1)) at hx
      linarith
    calc
      Measure.pi μs {x | (∫ z, empMean z ∂(Measure.pi μs))
          > empMean x + Real.sqrt (2 * sampleVar x * Real.log (2 / δ) / n)
            + 7 * Real.log (2 / δ) / (3 * ((n : ℝ) - 1))}
          ≤ Measure.pi μs (B ∪ C) := measure_mono hsub
      _ ≤ Measure.pi μs B + Measure.pi μs C := measure_union_le _ _
      _ ≤ ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) := add_le_add hB hC
      _ = ENNReal.ofReal δ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
