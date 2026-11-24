-- Prove2me | solution 1 for CompanionTheory.ThKR.Mp.MpE.eventually_det_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:30:39.489679+00:00
-- url     : https://prove2.me/submissions/57d3d70c-5edf-4793-816c-84eb1c4f4166

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MetaplecticGroupT2Space
import Theorems.Thm_P2M_CompanionTheory_ThKR_Mp_MpE_toBlocks___one__0a88a243d007

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology CompanionTheory.ThKR.LL
open scoped Real ContDiff
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
open CompanionTheory.ThKR.Mp.MpE
namespace CompanionTheory.ThKR.Mp.MpE
theorem _root_.solution : ∀ᶠ s in 𝓝 (1 : Sp l), 0 < s.1.toBlocks₁₁.det := by
  have hc : Continuous fun s : Sp l => s.1.toBlocks₁₁.det :=
    Continuous.matrix_det (continuous_pi fun i => continuous_pi fun j =>
      continuous_subtype_val.matrix_elem (Sum.inl i) (Sum.inl j))
  have h1 : (1 : Sp l).1.toBlocks₁₁.det = 1 := by
    rw [show (1 : Sp l).1 = 1 from rfl, toBlocks₁₁_one', Matrix.det_one]
  have h2 : ∀ᶠ y in 𝓝 ((1 : Sp l).1.toBlocks₁₁.det), (0 : ℝ) < y := lt_mem_nhds (by rw [h1]; exact one_pos)
  exact (hc.tendsto 1).eventually h2
end CompanionTheory.ThKR.Mp.MpE
