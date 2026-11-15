-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a282_scalar_small_modulus_expected_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:25:49.256171+00:00
-- url     : https://prove2.me/submissions/3a9e5d7c-9d90-48a5-8f64-2fa987e5b165

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    (F : ℝ → ℕ → ℝ) (A B : ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hAB : Tendsto (fun m => A m+B m) atTop (𝓝 (0:ℝ)))
    (hMod : ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ m,
      F δ m ≤ ε*K+A m+B m) :
    ∀ η, 0 < η → ∃ δ, 0 < δ ∧ ∃ k : ℕ, ∀ m, k ≤ m →
      F δ m ≤ η := by
  intro η hη
  have hDen : 0 < 2*(K+1) := by positivity
  have hε : 0 < η/(2*(K+1)) := by positivity
  obtain ⟨δ,hδ,hBound⟩ := hMod (η/(2*(K+1))) hε
  obtain ⟨k,hk⟩ :=
    (Metric.tendsto_atTop.1 hAB) (η/2) (by positivity)
  refine ⟨δ,hδ,k,?_⟩
  intro m hm
  have hSmall : A m+B m < η/2 := by
    have h := hk m hm
    have hd : |A m+B m| < η/2 := by
      simpa only [Real.dist_eq,sub_zero] using h
    linarith [le_abs_self (A m+B m)]
  have hEnergy : (η/(2*(K+1)))*K ≤ η/2 := by
    have hEq : (η/(2*(K+1)))*K = (η*K)/(2*(K+1)) := by ring
    rw [hEq]
    apply (div_le_iff₀ hDen).2
    nlinarith
  linarith [hBound m]
