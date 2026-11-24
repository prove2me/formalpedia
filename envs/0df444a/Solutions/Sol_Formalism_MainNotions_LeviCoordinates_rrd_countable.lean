-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rrd_countable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:41:35.670987+00:00
-- url     : https://prove2.me/submissions/731a54a2-7975-4baa-8ad6-f5a32e7fb85b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrdStronglyMeasurable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.LeviCoordinates
open MeasureTheory Filter Topology Set TopologicalSpace
open scoped InnerProductSpace
namespace Formalism.MainNotions.LeviCoordinates
theorem _root_.solution {ι : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [SeparableSpace H]
    {v : ι → H} (hv : Orthonormal ℂ v) : Countable ι := by
  have hsep : ∀ i j, i ≠ j → 1 ≤ ‖v i - v j‖ := by
    intro i j hij
    have h2 : ‖v i - v j‖ ^ 2 = 2 := by
      first
      | rw [norm_sub_sq (𝕜 := ℂ), hv.1 i, hv.1 j, hv.2 hij]; norm_num
      | rw [@norm_sub_sq ℂ, hv.1 i, hv.1 j, hv.2 hij]; norm_num
    nlinarith [norm_nonneg (v i - v j)]
  have hdisj : (Set.univ : Set ι).PairwiseDisjoint (fun i => Metric.ball (v i) (1 / 2 : ℝ)) := by
    intro i _ j _ hij
    show Disjoint (Metric.ball (v i) (1 / 2 : ℝ)) (Metric.ball (v j) (1 / 2 : ℝ))
    refine Set.disjoint_left.2 fun w hwi hwj => ?_
    have h1 := hsep i j hij
    rw [Metric.mem_ball] at hwi hwj
    have h3 : dist (v i) (v j) < 1 := by
      calc dist (v i) (v j) ≤ dist (v i) w + dist w (v j) := dist_triangle _ _ _
        _ = dist w (v i) + dist w (v j) := by rw [dist_comm (v i) w]
        _ < 1 / 2 + 1 / 2 := add_lt_add hwi hwj
        _ = 1 := by norm_num
    rw [dist_eq_norm] at h3
    linarith
  have hc := hdisj.countable_of_isOpen (fun i _ => Metric.isOpen_ball)
    (fun i _ => ⟨v i, Metric.mem_ball_self (by norm_num)⟩)
  exact Set.countable_univ_iff.1 hc
end Formalism.MainNotions.LeviCoordinates
