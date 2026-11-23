-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx10.pull
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:49:28.512845+00:00
-- url     : https://prove2.me/submissions/8ca4abc3-2b66-4a43-87bd-78d6365e5bc8

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevToThreshold

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx10
namespace Formalism.FourierDecayAlt.P.Jx10
theorem _root_.solution {α X : Type} [DecidableEq X] (η : α → X) (F : Finset α) (k : X → X → ℂ)
    (h : A5.IsPSD (F.image η) k) : A5.IsPSD F (fun x y => k (η x) (η y)) := by
  unfold Formalism.FourierDecayAlt.A5.IsPSD at h ⊢
  intro a
  show (∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k (η x) (η y)).im = 0 ∧
    0 ≤ (∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k (η x) (η y)).re
  set b : X → ℂ := fun u => ∑ z ∈ F.filter (fun z => η z = u), a z with hb
  have hmaps : ∀ x ∈ F, η x ∈ F.image η := fun x hx => Finset.mem_image_of_mem η hx
  have rhs : ∀ u v, b u * conj (b v) * k u v =
      ∑ x ∈ F.filter (fun z => η z = u), ∑ y ∈ F.filter (fun z => η z = v),
        a x * conj (a y) * k (η x) (η y) := by
    intro u v
    simp only [hb]
    rw [map_sum, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun y hy => ?_)
    have h1 := (Finset.mem_filter.mp hx).2
    have h2 := (Finset.mem_filter.mp hy).2
    rw [h1, h2] <;> ring
  have key : (∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k (η x) (η y)) =
      ∑ u ∈ F.image η, ∑ v ∈ F.image η, b u * conj (b v) * k u v := by
    simp_rw [rhs]
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_fiberwise_of_maps_to hmaps]
  rw [key]
  exact h b
end Formalism.FourierDecayAlt.P.Jx10
