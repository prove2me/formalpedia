-- Prove2me | solution 1 for FiniteEnergyPlane.exists_isLeftCutoff
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-12T18:13:40.740165+00:00
-- url     : https://prove2.me/submissions/8a797f14-f980-43f2-babf-a907f0e04a57

import Definitions.Def_FiniteEnergyPlane_TubeFamily



/-!
# Q-W1, Q-W2: slope weights and the left cut-off exist (proofs of the sorry'd children in
`Scratch/JWQ_Stmts.lean`, under the namespace `FiniteEnergyPlane.QW`).
-/

namespace FiniteEnergyPlane.QW

open Filter Topology
open scoped ContDiff

theorem exists_isSlopeWeight (a b : ℝ) : ∃ χ : ℝ → ℝ, IsSlopeWeight χ a b := by
  refine ⟨fun s => a * s + (b - a) * (Real.smoothTransition (s + 1 / 2) * s), ?_, ?_, ?_⟩
  · have h1 : ContDiff ℝ ∞ (fun s : ℝ => Real.smoothTransition (s + 1 / 2)) :=
      Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)
    fun_prop
  · intro s hs
    have hev : (fun s => a * s + (b - a) * (Real.smoothTransition (s + 1 / 2) * s)) =ᶠ[𝓝 s]
        fun s => a * s := by
      filter_upwards [Iio_mem_nhds (show s < -1 / 2 by linarith)] with y hy
      rw [Real.smoothTransition.zero_of_nonpos (by simp only [Set.mem_Iio] at hy; linarith)]
      ring
    rw [hev.deriv_eq]
    simpa using (hasDerivAt_id s).const_mul a |>.deriv
  · intro s hs
    have hev : (fun s => a * s + (b - a) * (Real.smoothTransition (s + 1 / 2) * s)) =ᶠ[𝓝 s]
        fun s => b * s := by
      filter_upwards [Ioi_mem_nhds (show (1 / 2 : ℝ) < s by linarith)] with y hy
      rw [Real.smoothTransition.one_of_one_le (by simp only [Set.mem_Ioi] at hy; linarith)]
      ring
    rw [hev.deriv_eq]
    simpa using (hasDerivAt_id s).const_mul b |>.deriv

theorem exists_isLeftCutoff : ∃ β : ℝ → ℝ, IsLeftCutoff β := by
  refine ⟨fun s => 1 - Real.smoothTransition (s + 1), ?_, ?_, ?_⟩
  · have h1 : ContDiff ℝ ∞ (fun s : ℝ => Real.smoothTransition (s + 1)) :=
      Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)
    fun_prop
  · intro s hs
    simp [Real.smoothTransition.zero_of_nonpos (show s + 1 ≤ 0 by linarith)]
  · intro s hs
    simp [Real.smoothTransition.one_of_one_le (show 1 ≤ s + 1 by linarith)]


end FiniteEnergyPlane.QW

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology CauchyRiemannIndex
open scoped ContDiff ENNReal Real

theorem solution : ∃ β : ℝ → ℝ, IsLeftCutoff β :=
  QW.exists_isLeftCutoff
