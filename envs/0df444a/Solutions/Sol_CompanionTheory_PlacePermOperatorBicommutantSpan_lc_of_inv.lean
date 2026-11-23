-- Prove2me | solution 1 for CompanionTheory.PlacePermOperatorBicommutantSpan.lc_of_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:02:40.813297+00:00
-- url     : https://prove2.me/submissions/faf3c20f-d7b2-4a81-8533-2746751d1b4c

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_IsOpenCoset
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_isOpen_coset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Set
open scoped ENNReal ComplexConjugate
noncomputable section
open CompanionTheory CompanionTheory.PlacePermOperatorBicommutantSpan
open GlobalTheory.CompanionTheory.SW.Core
variable {V : Type} [AddCommGroup V] [TopologicalSpace V]
variable [IsTopologicalAddGroup V]
namespace CompanionTheory.PlacePermOperatorBicommutantSpan
theorem _root_.solution {f : V → ℂ} {L : AddSubgroup V} (h : IsOpen (L : Set V)) (hf : ∀ x, ∀ l ∈ L, f (x + l) = f x) :
    IsLocallyConstant f :=
  (IsLocallyConstant.iff_exists_open f).2 fun x => ⟨{y | y - x ∈ L}, isOpen_coset x h, by simp, fun y hy => by
    have := hf x _ hy
    rwa [add_sub_cancel] at this⟩
end CompanionTheory.PlacePermOperatorBicommutantSpan
