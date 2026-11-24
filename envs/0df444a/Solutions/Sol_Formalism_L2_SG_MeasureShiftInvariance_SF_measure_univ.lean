-- Prove2me | solution 1 for Formalism.L2.SG.MeasureShiftInvariance.SF_measure_univ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:17:52.868653+00:00
-- url     : https://prove2.me/submissions/4243b062-a81b-4db7-b295-758d6bcd75c6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_CountableConjSub
import Theorems.Thm_Formalism_L2_SG_MeasureShiftInvariance_isFD_of_SF
import Theorems.Thm_Formalism_L2_SG_MeasureShiftInvariance_fd_instances

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal Pointwise
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.MeasureShiftInvariance
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
namespace Formalism.L2.SG.MeasureShiftInvariance
theorem _root_.solution (Γ : Subgroup G) [Countable Γ] (ν : Measure G)
    (hν : ∀ s ∈ Γ, ν.map (fun x => s * x) = ν) {Ω : Set G} (hΩ : SF (Γ : Set G) Ω) :
    ν Set.univ = ∑' _g : Γ, ν Ω := by
  obtain ⟨i1, i2⟩ := fd_instances Γ ν hν
  have hfd := isFD_of_SF Γ hΩ ν
  first
  | (rw [hfd.measure_eq_tsum Set.univ]; simp [Set.smul_set_univ])
  | (rw [hfd.measure_eq_tsum' Set.univ]; simp [measure_smul])
end Formalism.L2.SG.MeasureShiftInvariance
