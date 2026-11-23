-- Prove2me | solution 1 for Formalism.FN.GjScaling.Gj_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:45:53.397645+00:00
-- url     : https://prove2.me/submissions/a2818b72-a4c2-4b93-a008-e468077d5979

import Definitions.Def_Formalism_SuccessiveMinima_DefsMink
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_GjScale
import Theorems.Thm_Formalism_FN_GjScaling_measurableSet_boxJ
import Theorems.Thm_Formalism_FN_GjScaling_fib_set_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory Module Metric Set
open scoped Pointwise ENNReal
noncomputable section
namespace Formalism.FN
namespace GjScaling
variable {ι : Type*} [Fintype ι]
section decomp
variable (n j : ℕ)
private theorem measure_eq_of_measurePreserving_symm_preimage {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν) (S : Set α) :
    μ S = ν (e.symm ⁻¹' S) := by
  have h : Measure.map e μ (e.symm ⁻¹' S) = μ (e ⁻¹' (e.symm ⁻¹' S)) := e.map_apply _
  rw [he.map_eq] at h
  rw [h]
  congr 1
  ext x
  simp
end decomp
end GjScaling
end Formalism.FN
end
end

set_option autoImplicit false
open MeasureTheory Module Metric Set
open scoped Pointwise ENNReal
noncomputable section
open Formalism Formalism.FN
open Formalism.FN.GjScaling
variable {ι : Type*} [Fintype ι]
variable (n j : ℕ)
namespace Formalism.FN.GjScaling
theorem _root_.solution (A : Set (Fin n → ℝ)) (hA : IsOpen A) :
    Gj n j A = ∫⁻ y, tm (fib n j A y) := by
  have hS : MeasurableSet (Formalism.FN.boxJ n j ∩ (A + Formalism.FN.latJ n j)) :=
    (measurableSet_boxJ n j).inter hA.add_right.measurableSet
  have hmp := measurePreserving_piEquivPiSubtypeProd (μ := fun _ : Fin n => (volume : Measure ℝ))
    (p := fun i : Fin n => (i : ℕ) < j)
  refine (measure_eq_of_measurePreserving_symm_preimage _ hmp
    (Formalism.FN.boxJ n j ∩ (A + Formalism.FN.latJ n j))).trans ?_
  rw [Measure.prod_apply_symm]
  · refine lintegral_congr fun y => ?_
    rw [tm, ← fib_set_eq]
    rfl
  · exact MeasurableEquiv.measurable _ hS
end Formalism.FN.GjScaling
