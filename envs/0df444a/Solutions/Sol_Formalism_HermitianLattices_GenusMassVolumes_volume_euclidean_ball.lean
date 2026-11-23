-- Prove2me | solution 1 for Formalism.HermitianLattices.GenusMassVolumes.volume_euclidean_ball
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:29:56.095134+00:00
-- url     : https://prove2.me/submissions/784f673c-de0f-4503-a0ec-b599adf1b3a4

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FourierTransformScaledInner
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.HermitianLattices.GenusMassVolumes
open MeasureTheory Module
open scoped FourierTransform
private lemma sublevel_set_eq_closed_ball (N : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    {x : EuclideanSpace ℝ (Fin N) | ‖x‖ ^ 2 ≤ t} = Metric.closedBall 0 (Real.sqrt t) := by
  ext x
  simp only [Set.mem_ofPred_eq, mem_closedBall_zero_iff]
  rw [Real.le_sqrt (norm_nonneg x) ht]
end Formalism.HermitianLattices.GenusMassVolumes
end

set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GenusMassVolumes
open MeasureTheory Module
open scoped FourierTransform
namespace Formalism.HermitianLattices.GenusMassVolumes
theorem _root_.solution : ball_volume := by
  intro n t ht
  rw [sublevel_set_eq_closed_ball _ t ht]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hs : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (2 * 0))) (Real.sqrt t) = Set.univ := by
      ext x
      have : x = 0 := by ext i; exact absurd i.2 (by simp)
      simp [this, Real.sqrt_nonneg]
    rw [hs]
    have hv : volume (Set.univ : Set (EuclideanSpace ℝ (Fin (2 * 0)))) = 1 := by
      have h1 := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin (2 * 0))
      have := h1.measure_preimage (s := Set.univ) MeasurableSet.univ.nullMeasurableSet
      rw [Set.preimage_univ] at this
      rw [this]
      have hpi : (Set.univ : Set (Fin (2 * 0) → ℝ)) = Set.pi Set.univ (fun _ => Set.univ) := by simp
      rw [hpi, volume_pi_pi]
      simp
    rw [hv]
    simp
  · have : Nonempty (Fin (2 * n)) := ⟨⟨0, by omega⟩⟩
    have : Nontrivial (EuclideanSpace ℝ (Fin (2 * n))) := by
      apply Module.nontrivial_of_finrank_pos (R := ℝ)
      simp; omega
    have hk : finrank ℝ (EuclideanSpace ℝ (Fin (2 * n))) = 2 * n := by simp
    rw [InnerProductSpace.volume_closedBall_of_dim_even hk, hk, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal (Real.sqrt_nonneg t),
      ENNReal.toReal_ofReal (by positivity), pow_mul, Real.sq_sqrt ht]
    ring
end Formalism.HermitianLattices.GenusMassVolumes
