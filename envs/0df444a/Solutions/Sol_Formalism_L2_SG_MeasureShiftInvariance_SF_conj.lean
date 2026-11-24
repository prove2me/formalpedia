-- Prove2me | solution 1 for Formalism.L2.SG.MeasureShiftInvariance.SF_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:26:04.349084+00:00
-- url     : https://prove2.me/submissions/b85dcbf7-ce5b-4678-8e9b-d944bdef7da3

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_CountableConjSub
import Theorems.Thm_Formalism_L2_SG_MeasureShiftInvariance_mem_conjSub

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
theorem _root_.solution {Γ : Subgroup G} {Ω : Set G} (hΩ : SF (Γ : Set G) Ω) :
    SF (conjSub h Γ : Set G) {r | h * r * h⁻¹ ∈ Ω} := by
  refine ⟨hΩ.1.preimage ((measurable_const_mul h).mul_const h⁻¹), fun x => ?_, fun x hx t ht htx => ?_⟩
  · obtain ⟨s, hs, hsx⟩ := hΩ.2.1 (h * x * h⁻¹)
    refine ⟨h⁻¹ * s * h, ?_, ?_⟩
    · show h⁻¹ * s * h ∈ conjSub h Γ
      rw [mem_conjSub]
      simpa [mul_assoc] using hs
    · show h * (h⁻¹ * s * h * x) * h⁻¹ ∈ Ω
      simpa [mul_assoc] using hsx
  · have ht' : h * t * h⁻¹ ∈ Γ := (mem_conjSub h).1 ht
    have h1 : (h * t * h⁻¹) * (h * x * h⁻¹) ∈ Ω := by simpa [mul_assoc] using htx
    have h2 : h * t * h⁻¹ = 1 := hΩ.2.2 (h * x * h⁻¹) hx (h * t * h⁻¹) ht' h1
    calc t = h⁻¹ * (h * t * h⁻¹) * h := by group
      _ = 1 := by rw [h2]; group
end Formalism.L2.SG.MeasureShiftInvariance
