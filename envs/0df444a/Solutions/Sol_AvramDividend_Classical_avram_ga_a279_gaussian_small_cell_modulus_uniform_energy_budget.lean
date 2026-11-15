-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a279_gaussian_small_cell_modulus_uniform_energy_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:31:31.74667+00:00
-- url     : https://prove2.me/submissions/c7630fe6-d29d-4ca3-81a3-a0257de9dd44

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a282_scalar_small_modulus_expected_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Small : ℝ → ℕ → Ω → ℝ)
    (E A B : ℕ → Ω → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hSI : ∀ δ, 0 < δ → ∀ m,
      Integrable (fun ω => max (Small δ m ω) 0) P)
    (hEI : ∀ m, Integrable (E m) P)
    (hAI : ∀ m, Integrable (A m) P)
    (hBI : ∀ m, Integrable (B m) P)
    (hEB : ∀ m, (∫ ω, E m ω ∂P) ≤ K)
    (hAL : Tendsto (fun m => ∫ ω, A m ω ∂P) atTop (𝓝 (0:ℝ)))
    (hBL : Tendsto (fun m => ∫ ω, B m ω ∂P) atTop (𝓝 (0:ℝ)))
    (hMod : ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ m ω,
      max (Small δ m ω) 0 ≤ ε * E m ω + A m ω + B m ω) :
    ∀ η, 0 < η → ∃ δ, 0 < δ ∧ ∃ k : ℕ, ∀ m, k ≤ m →
      (∫ ω, max (Small δ m ω) 0 ∂P) ≤ η := by
  have hAB : Tendsto
      (fun m => (∫ ω, A m ω ∂P)+(∫ ω, B m ω ∂P))
        atTop (𝓝 (0:ℝ)) := by
    simpa only [add_zero] using hAL.add hBL
  apply avram_ga_a282_scalar_small_modulus_expected_budget
    (fun δ m => ∫ ω, max (Small δ m ω) 0 ∂P)
    (fun m => ∫ ω, A m ω ∂P)
    (fun m => ∫ ω, B m ω ∂P) K hK hAB
  intro ε hε
  obtain ⟨δ,hδ,hPt⟩ := hMod ε hε
  refine ⟨δ,hδ,?_⟩
  intro m
  have hEI' := (hEI m).const_mul ε
  have hAB' := hEI'.add (hAI m)
  have hEAB := hAB'.add (hBI m)
  have hUpper :
      (∫ ω, max (Small δ m ω) 0 ∂P) ≤
        ε*(∫ ω, E m ω ∂P) +
          (∫ ω, A m ω ∂P)+(∫ ω, B m ω ∂P) := by
    calc
      (∫ ω, max (Small δ m ω) 0 ∂P) ≤
          ∫ ω, ε*E m ω+A m ω+B m ω ∂P :=
        integral_mono (hSI δ hδ m) hEAB (hPt m)
      _ = ε*(∫ ω, E m ω ∂P) +
            (∫ ω, A m ω ∂P)+(∫ ω, B m ω ∂P) := by
        have h1 : (∫ ω, ε*E m ω+A m ω+B m ω ∂P) =
            (∫ ω, ε*E m ω+A m ω ∂P)+(∫ ω, B m ω ∂P) := by
          simpa only [Pi.add_apply] using integral_add hAB' (hBI m)
        have h2 : (∫ ω, ε*E m ω+A m ω ∂P) =
            (∫ ω, ε*E m ω ∂P)+(∫ ω, A m ω ∂P) := by
          simpa only [Pi.add_apply] using integral_add hEI' (hAI m)
        rw [h1,h2]
        rw [integral_const_mul]
  have hC : ε*(∫ ω, E m ω ∂P) ≤ ε*K :=
    mul_le_mul_of_nonneg_left (hEB m) hε.le
  linarith
