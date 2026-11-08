-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual10_original_monotone_R_mesh_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:31:26.963598+00:00
-- url     : https://prove2.me/submissions/aedd6ad0-35b6-44e8-a0df-d438c9bcd9e6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_weighted_R_variation_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- On a monotone physical mesh, the total variation of a monotone original
BV drift remainder telescopes to one endpoint difference. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (u : ℕ → ℕ → ℝ≥0) (n : ℕ)
    (hu : ∀ i, i < n + 1 → u n i ≤ u n (i + 1))
    (hRmono : Monotone (fun t : ℝ≥0 =>
      ((t : ℝ) * X.drift - X.X t ω) -
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0)))
    (a : ℕ → ℝ) (K : ℝ)
    (hK : ∀ i ∈ Finset.range (n + 1), |a i| ≤ K) :
    let J : ℝ≥0 → ℝ := fun t =>
      ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
      else 0
    let R : ℝ≥0 → ℝ := fun t =>
      ((t : ℝ) * X.drift - X.X t ω) - J t
    |∑ i ∈ Finset.range (n + 1),
      a i * (R (u n i) - R (u n (i + 1)))| ≤
        K * (R (u n (n + 1)) - R (u n 0)) := by
  classical
  let J : ℝ≥0 → ℝ := fun t =>
    ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
      Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
    else 0
  let R : ℝ≥0 → ℝ := fun t =>
    ((t : ℝ) * X.drift - X.X t ω) - J t
  change |∑ i ∈ Finset.range (n + 1),
      a i * (R (u n i) - R (u n (i + 1)))| ≤
        K * (R (u n (n + 1)) - R (u n 0))
  have hmono : Monotone R := hRmono
  have hsum :
      (∑ i ∈ Finset.range (n + 1),
        |R (u n i) - R (u n (i + 1))|) =
          R (u n (n + 1)) - R (u n 0) := by
    calc
      _ = ∑ i ∈ Finset.range (n + 1),
          (R (u n (i + 1)) - R (u n i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [abs_sub_comm]
        exact abs_of_nonneg (sub_nonneg.mpr (hmono (hu i (Finset.mem_range.mp hi))))
      _ = R (u n (n + 1)) - R (u n 0) :=
        Finset.sum_range_sub (fun i => R (u n i)) (n + 1)
  calc
    |∑ i ∈ Finset.range (n + 1),
        a i * (R (u n i) - R (u n (i + 1)))| ≤
      K * ∑ i ∈ Finset.range (n + 1),
        |R (u n i) - R (u n (i + 1))| := by
          exact avram_bv_residual10_original_weighted_R_variation_bound X ω u n a K hK
    _ = K * (R (u n (n + 1)) - R (u n 0)) := by rw [hsum]
