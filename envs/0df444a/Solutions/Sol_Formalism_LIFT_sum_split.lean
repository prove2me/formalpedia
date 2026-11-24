-- Prove2me | solution 1 for Formalism.LIFT.sum_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:32:00.035297+00:00
-- url     : https://prove2.me/submissions/21341136-4b76-43ce-8dd9-0ae7395ada99

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_CompsOfMemMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LIFT
open Finset
variable {ℓ : ℕ} {A : Type} [CommRing A] (φA : A →+* A) (ε : A) (aa : Ideal A)
namespace Formalism.LIFT
theorem _root_.solution {M : Type} [AddCommMonoid M] (F : ℕ → M) (a N : ℕ) :
    ∑ i : Fin a, ∑ j ∈ range N, F (i + a * j) = ∑ k ∈ range (a * N), F k := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.mul_succ, sum_range_add, ← ih]
    simp only [sum_range_succ, sum_add_distrib]
    congr 1
    rw [Finset.sum_range (fun x => F (a * N + x))]
    refine sum_congr rfl fun i _ => ?_
    rw [add_comm]
end Formalism.LIFT
