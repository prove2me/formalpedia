-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_g_isometry_original_finite_grid_predictable_L2_distance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T21:45:13.053068+00:00
-- url     : https://prove2.me/submissions/479de00a-11ca-498a-9ed1-8d1304f5a9b9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_finite_grid_from_physical_ordered_pairs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical ProbabilityTheory
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

/-- L2 distance between two physical intrinsic finite-grid compensated sums. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (ε : ℝ) (hε : 0 < ε) (B : ℕ → Set ℝ)
    (hB : ∀ i, MeasurableSet (B i))
    (hBand : ∀ i, B i ⊆ Ioo (-1 : ℝ) (-ε))
    (hν : ∀ i, X.ν (B i) < ⊤)
    (N : ℕ → Ω → ℝ≥0∞)
    (hActual : ∀ i, N i = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ B i))
    (r : ℕ → ℝ)
    (hRate : ∀ i, r i =
      (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)).toReal)
    (H G : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[𝓕 (grid i)] (H i))
    (hG : ∀ i, StronglyMeasurable[𝓕 (grid i)] (G i))
    (hHInf : ∀ i, MemLp (H i) ⊤ P)
    (hGInf : ∀ i, MemLp (G i) ⊤ P)
    (hCountEndpoint : ∀ i, StronglyMeasurable[𝓕 (grid (i + 1))]
      (fun ω => (N i ω).toReal))
    (K : ℕ → Ω → ℝ≥0∞)
    (hKMeas : ∀ i, Measurable (K i))
    (hPhysicalPair : ∀ i ω,
      (N i ω).toReal * ((N i ω).toReal - 1) = 2 * (K i ω).toReal)
    (hPairMean : ∀ i,
      (∫⁻ ω, K i ω ∂P) = ENNReal.ofReal
        (((((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
          X.ν (B i)).toReal) ^ 2 / 2))
    (mFuture : ℕ → MeasurableSpace Ω)
    (hFuture : ∀ i, mFuture i ≤ mΩ)
    (hSqMeas : ∀ i, StronglyMeasurable[mFuture i]
      (fun ω => ((N i ω).toReal - r i) ^ 2))
    (hIndependent : ∀ i, Indep (mFuture i) (𝓕 (grid i)) P)
    (n : ℕ) :
    (∫ ω, ((∑ i ∈ Finset.range n,
         H i ω * ((N i ω).toReal - r i)) -
       (∑ i ∈ Finset.range n,
         G i ω * ((N i ω).toReal - r i))) ^ 2 ∂P) =
      ∑ i ∈ Finset.range n, r i * ∫ ω, (H i ω - G i ω) ^ 2 ∂P := by
  let Q : ℕ → Ω → ℝ := fun i ω => H i ω - G i ω
  let D : ℕ → Ω → ℝ := fun i ω => Q i ω * ((N i ω).toReal - r i)
  have hQSM (i : ℕ) : StronglyMeasurable[𝓕 (grid i)] (Q i) :=
    (hH i).sub (hG i)
  have hQInf (i : ℕ) : MemLp (Q i) ⊤ P :=
    (hHInf i).sub (hGInf i)
  have hIso :=
    avram_p4_g_isometry_original_finite_grid_from_physical_ordered_pairs
      X grid hGrid ε hε B hB hBand hν N hActual
      r hRate Q D (by intro i ω; rfl) hQSM hQInf
      hCountEndpoint K hKMeas hPhysicalPair hPairMean
      mFuture hFuture hSqMeas hIndependent n
  have hSum (ω : Ω) :
      (∑ i ∈ Finset.range n, H i ω * ((N i ω).toReal - r i)) -
      (∑ i ∈ Finset.range n, G i ω * ((N i ω).toReal - r i)) =
      ∑ i ∈ Finset.range n, D i ω := by
    calc
      _ = ∑ i ∈ Finset.range n,
          (H i ω * ((N i ω).toReal - r i) -
           G i ω * ((N i ω).toReal - r i)) := by
        rw [Finset.sum_sub_distrib]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        dsimp [D, Q]
        ring
  calc
    _ = ∫ ω, (∑ i ∈ Finset.range n, D i ω) ^ 2 ∂P := by
      congr 1
      funext ω
      exact congrArg (fun x : ℝ => x ^ 2) (hSum ω)
    _ = _ := by simpa only [Q] using hIso
