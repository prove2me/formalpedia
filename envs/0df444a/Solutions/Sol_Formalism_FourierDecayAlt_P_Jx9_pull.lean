-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx9.pull
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:58:38.959798+00:00
-- url     : https://prove2.me/submissions/03c3186b-7c77-41f3-a049-a0b196b0dc3b

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AxiomsFromFamilies

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx9
variable {α X : Type}
namespace Formalism.FourierDecayAlt.P.Jx9
theorem _root_.solution [DecidableEq X] (η : α → X) (F : Finset α) (k : X → X → ℂ) (h : A5.IsPSD (F.image η) k) :
    A5.IsPSD F (fun x y => k (η x) (η y)) := by
  intro a
  set b : X → ℂ := fun x' => ∑ x ∈ F with η x = x', a x with hb
  have inner : ∀ (c : ℂ) (x' : X), ∑ y' ∈ F.image η, c * conj (b y') * k x' y' =
      ∑ y ∈ F, c * conj (a y) * k x' (η y) := by
    intro c x'
    apply Finset.sum_image'
    intro i _
    simp only [hb, map_sum, mul_sum, sum_mul]
    exact sum_congr rfl fun j hj => by rw [(mem_filter.1 hj).2]
  have key : ∑ x' ∈ F.image η, ∑ y' ∈ F.image η, b x' * conj (b y') * k x' y' =
      ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k (η x) (η y) := by
    apply Finset.sum_image'
    intro i _
    rw [inner]
    simp only [hb, sum_mul]
    rw [sum_comm]
    exact sum_congr rfl fun j hj => by rw [(mem_filter.1 hj).2]
  rw [← key]; exact h b
end Formalism.FourierDecayAlt.P.Jx9
