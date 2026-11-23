-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x6.psd_comap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:04:25.84319+00:00
-- url     : https://prove2.me/submissions/41b8041c-15db-4bd8-a5c6-58f5c60aaf05

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option maxHeartbeats 400000
noncomputable section
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P
namespace A5x6
section KRfacts
variable {K : Type} [CommRing K] (R : Subring K)
end KRfacts
private lemma sum_mul_comp_eq_sum_image_filter {X Y : Type} [DecidableEq Y] (F : Finset X) (f : X → Y)
    (a : X → ℂ) (g : Y → ℂ) :
    ∑ x ∈ F, a x * g (f x) =
      ∑ y ∈ F.image f, (∑ x ∈ F.filter (fun x => f x = y), a x) * g y := by
  rw [← Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem f hx)
    (fun x => a x * g (f x))]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [(Finset.mem_filter.mp hx).2]
end A5x6
open A5x6
end Formalism.FourierDecayAlt.P
end
end

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A5x6
namespace Formalism.FourierDecayAlt.P.A5x6
theorem _root_.solution {X Y : Type} [DecidableEq Y] (k : Y → Y → ℂ) (f : X → Y) (F : Finset X)
    (h : IsPSD (F.image f) k) : IsPSD F (fun x y => k (f x) (f y)) := by
  unfold IsPSD at h ⊢
  intro a
  obtain ⟨h1, h2⟩ := h (fun z => ∑ u ∈ F.filter (fun u => f u = z), a u)
  have e1 : ∀ z, ∑ y ∈ F, conj (a y) * k z (f y) =
      ∑ w ∈ F.image f, conj (∑ u ∈ F.filter (fun u => f u = w), a u) * k z w := by
    intro z
    rw [sum_mul_comp_eq_sum_image_filter F f (fun y => conj (a y)) (k z)]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [map_sum]
  have key : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k (f x) (f y) =
      ∑ x ∈ F.image f, ∑ y ∈ F.image f, (∑ u ∈ F.filter (fun u => f u = x), a u) *
        conj (∑ u ∈ F.filter (fun u => f u = y), a u) * k x y := by
    calc ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k (f x) (f y)
        = ∑ x ∈ F, a x * ∑ y ∈ F, conj (a y) * k (f x) (f y) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          ring
      _ = ∑ z ∈ F.image f, (∑ u ∈ F.filter (fun u => f u = z), a u) *
            ∑ y ∈ F, conj (a y) * k z (f y) :=
          sum_mul_comp_eq_sum_image_filter F f a (fun z => ∑ y ∈ F, conj (a y) * k z (f y))
      _ = _ := by
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [e1 z, Finset.mul_sum]
          refine Finset.sum_congr rfl fun w _ => ?_
          ring
  rw [key]
  exact ⟨h1, h2⟩
end Formalism.FourierDecayAlt.P.A5x6
