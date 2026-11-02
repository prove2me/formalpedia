-- Prove2me | solution 1 for FiniteEnergyPlane.hasLoopWind_mul
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-01T20:36:32.251996+00:00
-- url     : https://prove2.me/submissions/96816ceb-6655-40c0-a9c2-e0238834912d

import Definitions.Def_FiniteEnergyPlane_Winding



namespace FiniteEnergyPlane

open scoped Real

theorem hasLoopWind_mul_aux {f g : ℝ → ℂ} {k m : ℤ} (hf : HasLoopWind f k)
    (hg : HasLoopWind g m) : HasLoopWind (fun t => f t * g t) (k + m) := by
  obtain ⟨hfc, hfp, hf0, θ, hθc, hθ, hθk⟩ := hf
  obtain ⟨hgc, hgp, hg0, φ, hφc, hφ, hφm⟩ := hg
  refine ⟨hfc.mul hgc, hfp.mul hgp, fun t => mul_ne_zero (hf0 t) (hg0 t),
    fun t => θ t + φ t, hθc.add hφc, fun t => ?_, ?_⟩
  · beta_reduce
    calc f t * g t = (‖f t‖ * Complex.exp (θ t * Complex.I)) *
          (‖g t‖ * Complex.exp (φ t * Complex.I)) := by rw [← hθ t, ← hφ t]
      _ = _ := by
        rw [norm_mul]
        push_cast
        rw [add_mul, Complex.exp_add]
        ring
  · push_cast
    linarith

end FiniteEnergyPlane

open FiniteEnergyPlane

theorem solution {f g : ℝ → ℂ} {k m : ℤ} (hf : HasLoopWind f k)
    (hg : HasLoopWind g m) : HasLoopWind (fun t => f t * g t) (k + m) :=
  hasLoopWind_mul_aux hf hg
