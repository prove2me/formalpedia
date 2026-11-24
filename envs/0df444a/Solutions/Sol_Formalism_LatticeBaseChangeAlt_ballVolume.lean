-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.ballVolume
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:35:22.184865+00:00
-- url     : https://prove2.me/submissions/d4d5c65b-5e68-4aaf-9718-b64316333a11

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_TransvectionIsometry
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_IntegralMulExpNegSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeBaseChangeAlt
open Finset MeasureTheory Filter Topology Set
namespace Formalism.LatticeBaseChangeAlt
theorem _root_.solution : BallVolume := by
  intro D rr hr
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD
    show volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 0)) rr) = _
    have hb : Metric.ball (0 : EuclideanSpace ℝ (Fin 0)) rr = Set.univ := by
      ext z
      simp only [mem_ball_zero_iff, Set.mem_univ, iff_true]
      have hz : ‖z‖ = 0 := by
        rw [EuclideanSpace.norm_eq]
        simp
      rw [hz]
      exact hr
    have hpar : parallelepiped (EuclideanSpace.basisFun (Fin 0) ℝ) = Set.univ := by
      ext z
      simp only [Set.mem_univ, iff_true]
      have hz : z = 0 := by
        rw [← norm_eq_zero, EuclideanSpace.norm_eq]
        simp
      rw [hz, mem_parallelepiped_iff]
      exact ⟨0, ⟨le_rfl, zero_le_one⟩, by simp⟩
    rw [hb, ← hpar, OrthonormalBasis.volume_parallelepiped]
    simp
  have : Nonempty (Fin (2 * D)) := ⟨⟨0, by omega⟩⟩
  rw [EuclideanSpace.volume_ball, Fintype.card_fin]
  have hg : Real.Gamma (((2 * D : ℕ) : ℝ) / 2 + 1) = (D.factorial : ℝ) := by
    rw [show ((2 * D : ℕ) : ℝ) / 2 + 1 = (D : ℝ) + 1 by push_cast; ring]
    exact Real.Gamma_nat_eq_factorial D
  have hs : Real.sqrt Real.pi ^ (2 * D) = Real.pi ^ D := by
    rw [pow_mul, Real.sq_sqrt Real.pi_pos.le]
  rw [hg, hs, ← ENNReal.ofReal_pow hr.le, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring
end Formalism.LatticeBaseChangeAlt
