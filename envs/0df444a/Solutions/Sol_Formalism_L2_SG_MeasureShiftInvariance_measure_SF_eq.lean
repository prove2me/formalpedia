-- Prove2me | solution 1 for Formalism.L2.SG.MeasureShiftInvariance.measure_SF_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:17:56.888548+00:00
-- url     : https://prove2.me/submissions/9be1e2fb-6950-455d-8bf2-a08722dbdbea

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_CountableConjSub
import Theorems.Thm_Formalism_L2_SG_MeasureShiftInvariance_isFD_of_SF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MeasureTheory
open scoped ENNReal Pointwise
namespace Formalism.L2.SG.MeasureShiftInvariance
section SF
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
private theorem measurableSMul_and_smulInvariantMeasure_subgroup (Γ : Subgroup G) (ν : Measure G)
    (hν : ∀ s ∈ Γ, ν.map (fun x => s * x) = ν) :
    MeasurableSMul Γ G ∧ SMulInvariantMeasure Γ G ν := by
  refine ⟨?_, ?_⟩
  · first
    | infer_instance
    | exact ⟨fun c => measurable_const_mul (c : G), fun x => (measurable_mul_const x).comp measurable_subtype_coe⟩
  · constructor
    intro c s hs
    have hc := hν (c : G) c.2
    calc ν ((fun x => c • x) ⁻¹' s) = (ν.map (fun x => (c : G) * x)) s :=
          (Measure.map_apply (measurable_const_mul (c : G)) hs).symm
      _ = ν s := by rw [hc]
variable (h : G)
end SF
section Unfold
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  {μ : Measure G} [SFinite μ] [μ.IsMulLeftInvariant] (ν : Measure G) [SFinite ν]
end Unfold
section Boch
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  {μ : Measure G} [SFinite μ] [μ.IsMulLeftInvariant] (ν : Measure G) [SFinite ν]
end Boch
section Shift
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
end Shift
section ShiftG
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
end ShiftG
end Formalism.L2.SG.MeasureShiftInvariance
end
end

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal Pointwise
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.MeasureShiftInvariance
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
namespace Formalism.L2.SG.MeasureShiftInvariance
theorem _root_.solution (Γ : Subgroup G) [Countable Γ] (ν : Measure G)
    (hν : ∀ s ∈ Γ, ν.map (fun x => s * x) = ν) {Ω Ω' : Set G} (h1 : SF (Γ : Set G) Ω)
    (h2 : SF (Γ : Set G) Ω') : ν Ω = ν Ω' := by
  obtain ⟨i1, i2⟩ := measurableSMul_and_smulInvariantMeasure_subgroup Γ ν hν
  exact (isFD_of_SF Γ h1 ν).measure_eq
    (isFD_of_SF Γ h2 ν)
end Formalism.L2.SG.MeasureShiftInvariance
