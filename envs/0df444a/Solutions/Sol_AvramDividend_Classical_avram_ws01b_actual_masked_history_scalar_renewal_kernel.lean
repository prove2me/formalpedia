-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01b_actual_masked_history_scalar_renewal_kernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T08:29:14.5501+00:00
-- url     : https://prove2.me/submissions/3832b88b-8aac-4788-930b-4f58372016a5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_monotone
import Theorems.Thm_AvramDividend_Classical_chat03_lower_survival_filtration_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_killed_scale_shifted_expectation_of_scalar_renewal_kernel

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

/-- The source-Lévy random-reserve Markov kernel transports genuine scalar
killed renewal through a complete historical survival flag. Past ruin is
encoded by a negative reserve, valid even when BV W(0) is positive. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (hTerminal : ∃ j : ℕ, τ j = T)
    (q x : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hScalar : ∀ h : ℝ,
      (∫⁻ y,
        (if ∀ j : ℕ, τ j ≤ T → 0 ≤ h + y (τ j)
         then ENNReal.ofReal
           (Real.exp (-(q * (T : ℝ))) * W (h + y T))
         else (0 : ℝ≥0∞))
        ∂(Measure.map (fun ω => (fun u : ℝ≥0 => X.X u ω)) P)) =
      ENNReal.ofReal (W h)) :
    (∫⁻ ω,
      (if ∀ v : ℝ≥0, v ≤ T →
        0 ≤ (if ∀ w : ℝ≥0, w ≤ s → 0 ≤ x + X.X w ω
             then x + X.X s ω else (-1 : ℝ)) +
           (X.X (s + v) ω - X.X s ω)
      then ENNReal.ofReal (Real.exp (-(q * (T : ℝ))) *
        W ((if ∀ w : ℝ≥0, w ≤ s → 0 ≤ x + X.X w ω
            then x + X.X s ω else (-1 : ℝ)) +
           (X.X (s + T) ω - X.X s ω)))
      else (0 : ℝ≥0∞)) ∂P) =
    ∫⁻ ω, if ∀ w : ℝ≥0, w ≤ s → 0 ≤ x + X.X w ω
       then ENNReal.ofReal (W (x + X.X s ω))
       else (0 : ℝ≥0∞) ∂P := by
  classical
  let A : Set Ω := {ω | ∀ w : ℝ≥0, w ≤ s → 0 ≤ x + X.X w ω}
  let H : Ω → ℝ := fun ω => if ω ∈ A then x + X.X s ω else -1
  have hSet :
      A = {ω | ∀ v : ℝ≥0, v ≤ s → ¬ X.X v ω < -x} := by
    ext ω
    simp only [A, mem_setOf_eq, not_lt]
    constructor
    · intro h v hv
      have hz := h v hv
      linarith
    · intro h v hv
      have hz := h v hv
      linarith
  have hA : MeasurableSet[𝓕 s] A := by
    rw [hSet]
    exact chat03_lower_survival_filtration_measurable X τ hCover (-x) s
  have hH : Measurable[𝓕 s] H := by
    dsimp [H]
    exact Measurable.ite hA
      (measurable_const.add (X.adapted s)) measurable_const
  have hKernel := chat04_killed_scale_shifted_expectation_of_scalar_renewal_kernel
    X s H hH τ T hCover hTerminal q W hW hScalar
  change (∫⁻ ω,
    if ∀ v : ℝ≥0, v ≤ T →
      0 ≤ H ω + (X.X (s + v) ω - X.X s ω)
    then ENNReal.ofReal (Real.exp (-(q * (T : ℝ))) *
      W (H ω + (X.X (s + T) ω - X.X s ω)))
    else (0 : ℝ≥0∞) ∂P) =
    ∫⁻ ω, if ω ∈ A then ENNReal.ofReal (W (x + X.X s ω))
      else (0 : ℝ≥0∞) ∂P
  rw [hKernel]
  have hMeasW : Measurable (fun h : ℝ => ENNReal.ofReal (W h)) :=
    ENNReal.measurable_ofReal.comp (scaleFunction_monotone X q W hW).measurable
  have hM : Measurable H := hH.mono (𝓕.le s) le_rfl
  rw [lintegral_map hMeasW hM]
  have hneg : W (-1) = 0 := hW.1 (-1) (by norm_num)
  change (∫⁻ ω, ENNReal.ofReal
      (W (if ω ∈ A then x + X.X s ω else (-1 : ℝ))) ∂P) =
    ∫⁻ ω, if ω ∈ A then ENNReal.ofReal (W (x + X.X s ω))
      else (0 : ℝ≥0∞) ∂P
  congr 1
  funext ω
  by_cases hw : ω ∈ A
  · simp [hw]
  · simp [hw, hneg]
