-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_f2_original_source_mesh_C1_remainder_from_local_derivative_oscillation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T18:31:59.967432+00:00
-- url     : https://prove2.me/submissions/f9b1e40e-87c4-4d06-ac67-ff9021147b05

import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_d_bvmesh_local_C1_taylor_from_derivative_oscillation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section


theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (ω : Ω) (u : ℕ → ℝ≥0) (n : ℕ)
    (ε : ℝ) :
    let J : ℝ≥0 → ℝ := fun t =>
      ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
      else 0
    let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
    let z : ℕ → ℝ := fun i =>
      x + X.X (u i) ω - rightLimit D (u i) ω
    let c : ℕ → ℝ := fun i => Y (u (i + 1)) - Y (u i)
    (∀ i, i < n →
      ∀ v ∈ Set.uIcc (z i) (z i + c i), DifferentiableAt ℝ w v) →
    (∀ i, i < n →
      IntervalIntegrable (deriv w) volume (z i) (z i + c i)) →
    (∀ i, i < n →
      ∀ v ∈ Set.uIoc (z i) (z i + c i),
        |deriv w v - deriv w (z i)| ≤ ε) →
    ∀ i, i < n →
      |w (z i + c i) - w (z i) - deriv w (z i) * c i| ≤
        ε * |c i| := by
  intro J Y z c hDiff hInt hOsc i hi
  have hTaylor :=
    avram_p3_d_bvmesh_local_C1_taylor_from_derivative_oscillation
      w (z i) (z i + c i) ε
      (hDiff i hi) (hInt i hi) (hOsc i hi)
  simpa only [add_sub_cancel_left] using hTaylor
