-- Prove2me | solution 1 for AvramDividend.Classical.p2m81_bv_history_killed_scale_real_ennreal_bridge_no_standing
-- status  : ACCEPTED   (prove)
-- author  : @RSoulat
-- created : 2026-11-22T16:51:52.664849+00:00
-- url     : https://prove2.me/submissions/d68202ae-fa61-474d-9e70-9293c6761229

import Theorems.Thm_AvramDividend_Classical_p2m81_bv_fixedTime_scale_integrable_of_root_no_standing
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
attribute [local instance] Classical.propDecidable

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (y : ℝ) (T : ℝ≥0)
    (hMeas : MeasurableSet {z : Ω | ∀ v : ℝ≥0, v ≤ T → 0 ≤ y + X.X v z}) :
    (∫⁻ ω, (if ∀ v : ℝ≥0, v ≤ T → 0 ≤ y + X.X v ω then
        ENNReal.ofReal (Real.exp (-(q * (T : ℝ))) * W (y + X.X T ω))
      else (0 : ℝ≥0∞)) ∂P) =
    ENNReal.ofReal (∫ ω, ({z : Ω | ∀ v : ℝ≥0, v ≤ T → 0 ≤ y + X.X v z}).indicator
        (fun z => Real.exp (-(q * (T : ℝ))) * W (y + X.X T z)) ω ∂P) := by
  let S : Set Ω := {ω | ∀ v : ℝ≥0, v ≤ T → 0 ≤ y + X.X v ω}
  let F : Ω → ℝ := fun ω => Real.exp (-(q * (T : ℝ))) * W (y + X.X T ω)
  have hF : Integrable F P :=
    (p2m81_bv_fixedTime_scale_integrable_of_root_no_standing X q φ hq hφ hroot W hW y T).const_mul _
  have hNonneg : 0 ≤ᵐ[P] S.indicator F := Filter.Eventually.of_forall fun ω => by
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω]
      exact mul_nonneg (Real.exp_pos _).le (hW.2.1 _ (hω T le_rfl))
    · simp [Set.indicator_of_notMem hω]
  change
    (∫⁻ ω, (if ω ∈ S then ENNReal.ofReal (F ω) else 0) ∂P) =
      ENNReal.ofReal (∫ ω, S.indicator F ω ∂P)
  rw [ofReal_integral_eq_lintegral_ofReal (hF.indicator hMeas) hNonneg]
  apply lintegral_congr
  intro ω
  change (if ω ∈ S then ENNReal.ofReal (F ω) else 0) = ENNReal.ofReal (S.indicator F ω)
  by_cases hω : ω ∈ S
  · simp only [if_pos hω, Set.indicator_of_mem hω]
  · simp only [if_neg hω, Set.indicator_of_notMem hω, ENNReal.ofReal_zero]
