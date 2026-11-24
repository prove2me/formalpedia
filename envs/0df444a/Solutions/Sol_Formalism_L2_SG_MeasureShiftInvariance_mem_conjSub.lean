-- Prove2me | solution 1 for Formalism.L2.SG.MeasureShiftInvariance.mem_conjSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:17:57.973328+00:00
-- url     : https://prove2.me/submissions/5c1e31f7-5f94-49cf-bba0-35e2882d1a3d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_CountableConjSub

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
variable (h : G)
namespace Formalism.L2.SG.MeasureShiftInvariance
theorem _root_.solution {Γ : Subgroup G} {s : G} : s ∈ conjSub h Γ ↔ h * s * h⁻¹ ∈ Γ := by
  unfold conjSub
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    simpa [mul_assoc] using hg
  · intro hs
    exact ⟨h * s * h⁻¹, hs, by simp [mul_assoc]⟩
end Formalism.L2.SG.MeasureShiftInvariance
