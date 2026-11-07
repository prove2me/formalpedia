-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux18_original_physical_negative_band_marked_laplace_collision
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T18:37:07.525901+00:00
-- url     : https://prove2.me/submissions/4baafc3e-0d3b-48ea-a6bc-a4931bf84ee7

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux18_local_negative_mark_collision
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! Pointwise Laplace linearisation of actual, finitely many marked negative jumps. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (n : ℕ) :
    let J : Set ℝ≥0 := {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}
    let S : Finset ℝ≥0 :=
      (AvramDividend.Classical.avram_wave7_06_original_negative_band_marked_times_finite
        X ω T n).toFinset
    0 ≤ Real.exp (∑ u ∈ S,
      (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) -
      (1 - ∑ u ∈ S,
        (1 - Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) ∧
    2 * (Real.exp (∑ u ∈ S,
      (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) -
      (1 - ∑ u ∈ S,
        (1 - Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) ≤
      (J.ncard : ℝ) * ((J.ncard : ℝ) - 1) := by
  classical
  let J : Set ℝ≥0 := {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
      -(1 / ((n : ℝ) + 1))}
  have hFin : J.Finite :=
    AvramDividend.Classical.avram_wave7_06_original_negative_band_marked_times_finite
      X ω T n
  let S : Finset ℝ≥0 := hFin.toFinset
  change 0 ≤ Real.exp (∑ u ∈ S,
      (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) -
      (1 - ∑ u ∈ S,
        (1 - Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) ∧
    2 * (Real.exp (∑ u ∈ S,
      (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) -
      (1 - ∑ u ∈ S,
        (1 - Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) ≤
      (J.ncard : ℝ) * ((J.ncard : ℝ) - 1)
  have hneg : ∀ u, u ∈ S →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤ 0 := by
    intro u hu
    have hmem : u ∈ J := (hFin.mem_toFinset).mp hu
    have hmark := hmem.2.2
    have hcut : -(1 / ((n : ℝ) + 1)) ≤ 0 :=
      neg_nonpos.mpr (by positivity)
    exact le_trans hmark hcut
  have h := AvramDividend.Classical.avram_redux18_local_negative_mark_collision
    S (fun u => X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) hneg
  have hcard : S.card = J.ncard :=
    (Set.ncard_eq_toFinset_card J hFin).symm
  simpa only [hcard] using h
