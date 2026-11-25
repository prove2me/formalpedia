-- Prove2me | solution 1 for Formalism.L2.SG.MeasureShiftInvariance.SF_transl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:12:11.030604+00:00
-- url     : https://prove2.me/submissions/a7321eab-fc5f-4c05-98be-21e8b2b0680a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_CountableConjSub
import Theorems.Thm_Formalism_L2_SG_MeasureShiftInvariance_SF_mul_right
import Theorems.Thm_Formalism_L2_SG_MeasureShiftInvariance_SF_conj

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
theorem _root_.solution {Γ : Subgroup G} {Ω : Set G} (hΩ : SF (Γ : Set G) Ω) (y : G) :
    SF (conjSub h Γ : Set G) {r | h * (r * y) ∈ Ω} := by
  have H := SF_mul_right (SF_conj h hΩ) (y * h)
  have hset : {r | h * (r * y) ∈ Ω} = {r | r * (y * h) ∈ {r | h * r * h⁻¹ ∈ Ω}} := by
    ext r
    simp [mul_assoc]
  rw [hset]
  exact H
end Formalism.L2.SG.MeasureShiftInvariance
