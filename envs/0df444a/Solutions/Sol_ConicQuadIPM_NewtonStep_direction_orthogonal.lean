-- Prove2me | solution 1 for ConicQuadIPM.NewtonStep.direction_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T04:00:08.735982+00:00
-- url     : https://prove2.me/submissions/a3c234f2-c5e1-44b7-8675-cf98a8026ae3

import Definitions.Def_ConicQuadIPM_NewtonStep_Setting
import Theorems.Thm_ConicQuadIPM_NewtonStep_eq_26
import Theorems.Thm_ConicQuadIPM_NewtonStep_p14_chain

set_option autoImplicit false
open Matrix ConicQuadIPM.Complementarity ConicQuadIPM.NewtonStep
theorem solution
    {m k : ℕ} (kind : Fin k → ConicQuadIPM.Complementarity.ConeKind) (n : Fin k → ℕ) (hwf : ConicQuadIPM.Complementarity.WellFormed kind n)
    (A : (i : Fin k) → Matrix (Fin m) (Fin (n i)) ℝ) (b : Fin m → ℝ)
    (c : (i : Fin k) → Fin (n i) → ℝ)
    (x0 : (i : Fin k) → Fin (n i) → ℝ) (τ0 : ℝ) (y0 : Fin m → ℝ)
    (s0 : (i : Fin k) → Fin (n i) → ℝ) (κ0 : ℝ) (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (dx : (i : Fin k) → Fin (n i) → ℝ) (dτ : ℝ) (dy : Fin m → ℝ)
    (ds : (i : Fin k) → Fin (n i) → ℝ) (dκ : ℝ)
    (h22 : NewtonSystem kind n A b c x0 τ0 y0 s0 κ0 γ dx dτ dy ds dκ) :
    (∑ i, dx i ⬝ᵥ ds i) + dτ * dκ = 0  := by
  obtain ⟨hz, hexp⟩ := eq_26 kind n hwf A b c x0 τ0 y0 s0 κ0 γ hγ dx dτ dy ds dκ h22
  have hc := p14_chain kind n hwf A b c x0 τ0 y0 s0 κ0 γ hγ dx dτ dy ds dκ h22
  have hmu : mu0 x0 τ0 s0 κ0 * ((k : ℝ) + 1) = (∑ i, x0 i ⬝ᵥ s0 i) + τ0 * κ0 := by
    unfold mu0
    exact div_mul_cancel₀ _ (by positivity)
  rw [mul_assoc, hmu] at hc
  rw [hc] at hexp
  have h := hz.trans hexp
  nlinarith only [h]

#print axioms solution
