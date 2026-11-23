-- Prove2me | solution 1 for Formalism.FN.GjScaling.tm_add_singleton
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:45:35.256507+00:00
-- url     : https://prove2.me/submissions/1d41d770-781e-4d34-89fe-e52822726632

import Definitions.Def_Formalism_SuccessiveMinima_DefsMink
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_GjScale
import Theorems.Thm_Formalism_FN_GjScaling_Zv_add
import Theorems.Thm_Formalism_FN_GjScaling_Zv_neg
import Theorems.Thm_Formalism_FN_GjScaling_mem_span_basisFun_iff
import Theorems.Thm_Formalism_FN_GjScaling_fundamentalDomain_eq
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
private theorem add_mem_add_intVectors_iff {T : Set (ι → ℝ)} {z : ι → ℝ} (hz : z ∈ Zv ι)
    (x : ι → ℝ) : z + x ∈ T + Zv ι ↔ x ∈ T + Zv ι := by
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    have hab' : a + b = z + x := hab
    refine ⟨a, ha, b + -z, Zv_add hb (Zv_neg hz), ?_⟩
    show a + (b + -z) = x
    rw [← add_assoc, hab', add_neg_cancel_comm]
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, z + b, Zv_add hz hb, by
      show a + (z + b) = z + (a + b)
      exact add_left_comm a z b⟩
section decomp
variable (n j : ℕ)
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
namespace Formalism.FN.GjScaling
theorem _root_.solution {B : Set (ι → ℝ)} (hB : IsOpen B) (c : ι → ℝ) :
    tm (B + {c}) = tm B := by
  have hF : IsAddFundamentalDomain (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))) (Qv ι)
      volume := by
    rw [← fundamentalDomain_eq]
    exact ZSpan.isAddFundamentalDomain _ _
  have hF' := hF.vadd_of_comm c
  have hW : MeasurableSet (B + {c} + Zv ι) := hB.add_right.add_right.measurableSet
  have hinv : ∀ g : Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι)),
      (fun x => g +ᵥ x) ⁻¹' (B + {c} + Zv ι) = B + {c} + Zv ι := fun g => by
    ext x
    exact add_mem_add_intVectors_iff ((mem_span_basisFun_iff _).1 g.2) x
  have : VAddInvariantMeasure (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))) (ι → ℝ) volume := by
    refine ⟨?_⟩
    intro g s _
    exact measure_preimage_add volume (g : ι → ℝ) s
  have : Countable (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))) := by
    refine Function.Injective.countable
      (f := fun g : Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι)) => fun i => ⌊(g : ι → ℝ) i⌋) ?_
    intro g g' hgg
    apply Subtype.ext
    funext i
    obtain ⟨m, hm⟩ := (mem_span_basisFun_iff _).1 g.2 i
    obtain ⟨m', hm'⟩ := (mem_span_basisFun_iff _).1 g'.2 i
    have := congrFun hgg i
    simp only [hm, hm', Int.floor_intCast] at this
    rw [hm, hm', this]
  have h1 := hF.measure_set_eq hF' hW hinv
  have hshift : B + {c} + Zv ι = (fun x => c + x) '' (B + Zv ι) := by
    rw [add_comm B, add_assoc, Set.singleton_add]
  have h2 : (B + {c} + Zv ι) ∩ (c +ᵥ Qv ι) =
      (fun x => c + x) '' ((B + Zv ι) ∩ Qv ι) := by
    rw [Set.image_inter (add_right_injective c), ← hshift]
    rfl
  unfold tm
  rw [Set.inter_comm (Qv ι) (B + {c} + Zv ι), h1, h2, Set.image_add_left,
    measure_preimage_add, Set.inter_comm (B + Zv ι)]
end Formalism.FN.GjScaling
