-- Prove2me | solution 1 for CompanionTheory.LimBd.URep.UnitaryRep.continuous_action
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:25:10.710933+00:00
-- url     : https://prove2.me/submissions/6e81ef77-b148-4ed7-82f4-dd5dbcc61735

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_URepBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.LimBd CompanionTheory.LimBd.URep
open scoped InnerProductSpace ComplexConjugate
open ContinuousLinearMap Filter Topology
open CompanionTheory.LimBd.URep.UnitaryRep
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
variable (π : UnitaryRep G H)
namespace CompanionTheory.LimBd.URep.UnitaryRep
theorem _root_.solution : Continuous fun p : G × H => π p.1 p.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨h, w⟩
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hle : ∀ p : G × H, ‖π p.1 p.2 - π h w‖ ≤ ‖p.2 - w‖ + ‖π p.1 w - π h w‖ := by
    intro p
    calc ‖π p.1 p.2 - π h w‖ = ‖π p.1 (p.2 - w) + (π p.1 w - π h w)‖ := by
          rw [map_sub]; congr 1; abel
      _ ≤ ‖π p.1 (p.2 - w)‖ + ‖π p.1 w - π h w‖ := norm_add_le _ _
      _ = ‖p.2 - w‖ + ‖π p.1 w - π h w‖ := by rw [norm_map]
  refine squeeze_zero (fun _ => norm_nonneg _) hle ?_
  rw [← add_zero (0 : ℝ)]
  refine Tendsto.add ?_ ?_
  · have : Tendsto (fun p : G × H => p.2) (𝓝 (h, w)) (𝓝 w) := continuous_snd.tendsto _
    rw [tendsto_iff_norm_sub_tendsto_zero] at this
    exact this
  · have : Tendsto (fun p : G × H => π p.1 w) (𝓝 (h, w)) (𝓝 (π h w)) :=
      ((π.continuous_orbit w).comp continuous_fst).tendsto _
    rw [tendsto_iff_norm_sub_tendsto_zero] at this
    exact this
end CompanionTheory.LimBd.URep.UnitaryRep
