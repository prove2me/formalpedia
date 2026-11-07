-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux19_original_strict_negative_marked_laplace_collision
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:34:49.397491+00:00
-- url     : https://prove2.me/submissions/643d1f68-8dcf-4537-bf19-6f2586690253

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_redux18_local_negative_mark_collision
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! The exact original strict negative-mark Laplace collision is quadratic. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (k : ℕ) :
    let J : Set ℝ≥0 := {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u <
        -(1 / ((k : ℝ) + 1))}
    let S : Finset ℝ≥0 :=
      (AvramDividend.Classical.avram_redux19_original_strict_negative_marked_times_finite
        X ω T k).toFinset
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
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u <
      -(1 / ((k : ℝ) + 1))}
  have hFin : J.Finite :=
    AvramDividend.Classical.avram_redux19_original_strict_negative_marked_times_finite
      X ω T k
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
    have hcut : -(1 / ((k : ℝ) + 1)) ≤ 0 :=
      neg_nonpos.mpr (by positivity)
    exact le_trans (le_of_lt hmark) hcut
  have h := AvramDividend.Classical.avram_redux18_local_negative_mark_collision
    S (fun u => X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) hneg
  have hcard : S.card = J.ncard :=
    (Set.ncard_eq_toFinset_card J hFin).symm
  simpa only [hcard] using h
