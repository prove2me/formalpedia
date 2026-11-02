-- Prove2me | solution 1 for FiniteEnergyPlane.hasLoopWind_conj
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-01T20:56:29.702047+00:00
-- url     : https://prove2.me/submissions/298aa9a8-6702-4f6e-a3de-1308ed2ccd6f

import Definitions.Def_FiniteEnergyPlane_Winding



namespace FiniteEnergyPlane

open scoped Real

theorem hasLoopWind_conj_aux {f : ℝ → ℂ} {k : ℤ} (hf : HasLoopWind f k) :
    HasLoopWind (fun t => starRingEnd ℂ (f t)) (-k) := by
  obtain ⟨hfc, hfp, hf0, θ, hθc, hθ, hθk⟩ := hf
  refine ⟨Complex.continuous_conj.comp hfc, fun t => by simp only [hfp t],
    fun t => by simpa using hf0 t, fun t => -θ t, hθc.neg, fun t => ?_, ?_⟩
  · beta_reduce
    rw [Complex.norm_conj]
    conv_lhs => rw [hθ t]
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
      Complex.conj_I]
    push_cast
    ring_nf
  · push_cast
    linarith

end FiniteEnergyPlane

open FiniteEnergyPlane

theorem solution {f : ℝ → ℂ} {k : ℤ} (hf : HasLoopWind f k) :
    HasLoopWind (fun t => starRingEnd ℂ (f t)) (-k) :=
  hasLoopWind_conj_aux hf
