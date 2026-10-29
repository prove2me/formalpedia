-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_cr_new_native_root_coefficient_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T00:05:02.338615+00:00
-- url     : https://prove2.me/submissions/039a59e5-30fc-4c18-887b-bbbce6c811d0

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_cr_new_levy_psi_hasDerivAt_positive
import Theorems.Thm_AvramDividend_Classical_esscher_levy_positive_root_derivative_lower
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_cr_new_native_positive_root_derivative_coefficient
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The native Esscher drift coefficient at a positive q-root is positive,
    quantitatively bounded below by the original-root secant q/φ. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    q / φ ≤ X.c - (X.ν.map (fun y : ℝ => -y)).real ({1} : Set ℝ) +
      X.σ ^ 2 * φ +
      (∫ z in Ioi (0 : ℝ), (if z ≤ 1 then z else 0) -
        z * Real.exp (-φ * z) ∂(X.ν.map (fun y : ℝ => -y))) ∧
      0 < X.c - (X.ν.map (fun y : ℝ => -y)).real ({1} : Set ℝ) +
      X.σ ^ 2 * φ +
      (∫ z in Ioi (0 : ℝ), (if z ≤ 1 then z else 0) -
        z * Real.exp (-φ * z) ∂(X.ν.map (fun y : ℝ => -y))) := by
  obtain ⟨m, hm⟩ :=
    avram_ws01e_cr_new_levy_psi_hasDerivAt_positive X φ hφ
  have heq :=
    avram_ws01e_cr_new_native_positive_root_derivative_coefficient
      X q φ m hφ hroot hm
  rw [← heq]
  exact esscher_levy_positive_root_derivative_lower X q φ m
    hq hφ hroot hm
