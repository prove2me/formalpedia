-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_04_compensated_ito_height_atomless_of_enumerated_stops
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:53:50.406181+00:00
-- url     : https://prove2.me/submissions/f8795c49-3333-4985-a856-a6f6b1956d21

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_root29_04_pure_jump_countable_stopped_height_null

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem solution
    {Ω E : Type*} [mΩ : MeasurableSpace Ω] [mE : MeasurableSpace E]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hvar : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (n : Measure E) (markHeight : E → ℝ≥0)
    (marks : ℕ → Ω → E) (τ ζ : ℕ → Ω → ℝ≥0) (x : ℝ≥0)
    (hτ : ∀ k : ℕ, ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] {ω : Ω | τ k ω ≤ s})
    (hstop : ∀ k : ℕ,
      IsStoppingTime 𝓕 (fun ω => (τ k ω : WithTop ℝ≥0)))
    (hAtLevel : ∀ k : ℕ, ∀ ω : Ω,
      markHeight (marks k ω) = x →
      τ k ω < ζ k ω ∧
      reflectedSup X (τ k ω) ω = (x : ℝ) ∧
      ∀ t : ℝ≥0, τ k ω ≤ t → t < ζ k ω →
        reflectedSup X t ω ≤ (x : ℝ))
    (times horizons : ℕ → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b →
      ∃ m : ℕ, a < times m ∧ times m < b)
    (hpos : ∀ k : ℕ, 0 < horizons k)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε →
      ∃ k : ℕ, horizons k ≤ ε)
    (L : Ω → ENNReal)
    (hLpos : 0 < ∫⁻ ω, L ω ∂P)
    (hComp : (∫⁻ ω, (∑' k : ℕ,
      if markHeight (marks k ω) = x then (1 : ENNReal) else 0) ∂P) =
      (∫⁻ ω, L ω ∂P) * n {e : E | markHeight e = x}) :
    n {e : E | markHeight e = x} = 0 := by
  have hnull := avram_root29_04_pure_jump_countable_stopped_height_null X hvar 0 le_rfl 0
    τ ζ (fun k ω => markHeight (marks k ω)) x hτ hstop hAtLevel times horizons hdense hpos hcofinal
  simp only [zero_mul, NNReal.coe_zero, sub_self, Real.exp_zero, ENNReal.ofReal_one] at hnull
  rw [show (fun _ : Ω => (1 : ℝ≥0∞)) = 1 from rfl, withDensity_one] at hnull
  have hae : ∀ᵐ ω ∂P, (∑' k : ℕ, if markHeight (marks k ω) = x then (1 : ENNReal) else 0) = 0 := by
    have := measure_eq_zero_iff_ae_notMem.mp hnull
    filter_upwards [this] with ω hω
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists] at hω
    simp [hω]
  rw [lintegral_congr_ae hae, lintegral_zero] at hComp
  exact ((mul_eq_zero.mp hComp.symm).resolve_left hLpos.ne')
