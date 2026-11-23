-- Prove2me | solution 1 for Formalism.HermitianLattices.ZeroFreeRegionGL2.weighted_sum_identity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:42:56.276525+00:00
-- url     : https://prove2.me/submissions/1c7be901-843e-46f2-8f41-40dfebd83422

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_WeightedVonMangoldtSumIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.ZeroFreeRegionGL2
theorem _root_.solution : WGIdentity := by
  intro q _ χ a w M ha hw hM
  unfold Gchi
  have hsub : Icc 1 ⌊a / w⌋₊ ⊆ Icc 1 M := Icc_subset_Icc le_rfl hM
  rw [← Finset.sum_subset hsub (f := fun n => ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) * ((max (a / n - w) 0 : ℝ) : ℂ))]
  · rw [mul_add, Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro n hn
      rw [mem_Icc] at hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
      have hle : (n : ℝ) ≤ a / w := (Nat.le_floor_iff (by positivity)).1 hn.2
      have h1 : w ≤ a / n := by rw [le_div_iff₀ hn0]; rw [le_div_iff₀ hw] at hle; linarith
      rw [max_eq_left (by linarith)]
      have : w * (a / w / n - 1) = a / n - w := by field_simp
      rw [← this]; push_cast; ring
    · have : (w : ℂ) ≠ 0 := by exact_mod_cast hw.ne'
      push_cast; field_simp
  · intro n hn hn'
    rw [mem_Icc] at hn hn'
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
    have : a / w < n := by
      by_contra hc
      exact hn' ⟨hn.1, Nat.le_floor (not_lt.1 hc)⟩
    have h1 : a / n ≤ w := by rw [div_le_iff₀ hn0]; rw [div_lt_iff₀ hw] at this; linarith
    rw [max_eq_right (by linarith)]; simp
end Formalism.HermitianLattices.ZeroFreeRegionGL2
