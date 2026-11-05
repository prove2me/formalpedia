-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_h_gaussian_original_real_quadratic_strip_uniform_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:38:51.60207+00:00
-- url     : https://prove2.me/submissions/43c76d77-da4f-4299-8a5a-209504d5a84d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_quadratic_strip_uniform_tail
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_nu_quadratic_real_energy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
/-- Actual real quadratic energy of all finite negative-jump strips vanishes uniformly. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ m : ℕ,
      IntegrableOn (fun z : ℝ => z ^ 2)
        (Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))) X.ν ∧
      (∫ z in Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1))),
        z ^ 2 ∂X.ν) < ε := by
  have hPos : (0 : ℝ≥0∞) < ENNReal.ofReal ε :=
    ENNReal.ofReal_pos.mpr hε
  obtain ⟨N, hBound⟩ :=
    avram_p4_h_gaussian_original_quadratic_strip_uniform_tail
      X (ENNReal.ofReal ε) hPos
  refine ⟨N, ?_⟩
  intro n hn m
  let C : Set ℝ :=
    Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
  let D : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) 0
  have hSub : C ⊆ D := by
    intro z hz
    refine ⟨hz.1, ?_⟩
    have hd : 0 ≤ (1 : ℝ) / ((m : ℝ) + 1) := by positivity
    linarith [hz.2]
  have hTailI := (avram_p4_h_gaussian_original_nu_quadratic_real_energy X n).1
  have hI : IntegrableOn (fun z : ℝ => z ^ 2) C X.ν :=
    hTailI.mono_set hSub
  have hNN : 0 ≤ᵐ[X.ν.restrict C] (fun z : ℝ => z ^ 2) :=
    Filter.Eventually.of_forall (fun z => sq_nonneg z)
  have hEq : ENNReal.ofReal (∫ z in C, z ^ 2 ∂X.ν) =
      ∫⁻ z in C, ENNReal.ofReal (z ^ 2) ∂X.ν :=
    ofReal_integral_eq_lintegral_ofReal hI hNN
  constructor
  · change Integrable (fun z : ℝ => z ^ 2) (X.ν.restrict C)
    exact hI
  · apply (ENNReal.ofReal_lt_ofReal_iff hε).1
    rw [hEq]
    exact hBound n hn m
