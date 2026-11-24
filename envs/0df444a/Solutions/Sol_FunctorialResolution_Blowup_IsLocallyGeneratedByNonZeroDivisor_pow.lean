-- Prove2me | solution 1 for FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor.pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:06:21.798802+00:00
-- url     : https://prove2.me/submissions/802f6ed9-2b08-4828-9611-813eb1dba0c6

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_ControlledTransform
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
variable {Y : Scheme.{u}}
private theorem mul_ideal_apply {Y' : Scheme.{u}} (F G : Y'.IdealSheafData)
    (U : Y'.affineOpens) : (F * G).ideal U = F.ideal U * G.ideal U := rfl
private theorem pow_ideal_apply {Y' : Scheme.{u}} (F : Y'.IdealSheafData) (n : ℕ)
    (U : Y'.affineOpens) : (F ^ n).ideal U = F.ideal U ^ n := by
  induction n with
  | zero => simp
  | succ m ih => rw [pow_succ, pow_succ, mul_ideal_apply, ih]
variable {X X₁ : Scheme.{u}}
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {Y : Scheme.{u}}
namespace FunctorialResolution.EmbeddedResolution
namespace _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor
theorem _root_.solution {F : Y.IdealSheafData} (hF : FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor F) (n : ℕ) :
    FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor (F ^ n) := by
  unfold FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor at hF ⊢
  intro x
  obtain ⟨U, f, hxU, hf, hFU⟩ := hF x
  refine ⟨U, f ^ n, hxU, pow_mem hf n, ?_⟩
  rw [EmbeddedResolution.pow_ideal_apply, hFU, Ideal.span_singleton_pow]
end _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor
end FunctorialResolution.EmbeddedResolution
