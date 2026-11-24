-- Prove2me | solution 1 for Formalism.HermitianLattices.GenusMassVolumes.sphere_surface_volume
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:56:53.640072+00:00
-- url     : https://prove2.me/submissions/4da0aa34-20b6-4333-af5b-80efaef60b77

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FourierTransformScaledInner
import Theorems.Thm_Formalism_HermitianLattices_GenusMassVolumes_volume_euclidean_ball

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GenusMassVolumes
open MeasureTheory Module
open scoped FourierTransform
namespace Formalism.HermitianLattices.GenusMassVolumes
theorem _root_.solution : SphereVolumeDerivative := by
  intro M hM
  have hev : (fun t : ℝ => (2 : ℝ) ^ M *
      (volume {x : EuclideanSpace ℝ (Fin (2 * M)) | ‖x‖ ^ 2 ≤ t}).toReal) =ᶠ[nhds 1]
      fun t : ℝ => (2 : ℝ) ^ M * (Real.pi ^ M * t ^ M / (M.factorial : ℝ)) := by
    filter_upwards [lt_mem_nhds (zero_lt_one' ℝ)] with t ht
    rw [volume_euclidean_ball M t ht.le]
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  have h1 : HasDerivAt (fun t : ℝ => t ^ M) ((M : ℝ) * 1 ^ (M - 1)) 1 := hasDerivAt_pow M 1
  have h2 := ((h1.const_mul (Real.pi ^ M)).div_const (M.factorial : ℝ)).const_mul ((2 : ℝ) ^ M)
  have he : (2 * Real.pi) ^ M / ((M - 1).factorial : ℝ) =
      2 ^ M * (Real.pi ^ M * ((M : ℝ) * 1 ^ (M - 1)) / (M.factorial : ℝ)) := by
    clear h2 h1 hev
    obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
    have hk : ((k.factorial : ℝ)) ≠ 0 := by positivity
    have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
    simp only [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      one_pow, mul_one]
    rw [mul_pow]
    field_simp
  rw [he]
  exact h2
end Formalism.HermitianLattices.GenusMassVolumes
