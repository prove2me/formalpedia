-- Prove2me | solution 1 for Formalism.LIFT.comps_mul_eps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:32:01.91633+00:00
-- url     : https://prove2.me/submissions/2185f726-0216-4629-b353-57a839d7cceb

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
theorem _root_.solution (hℓ : 0 < ℓ) (hε : φA ε = ε ^ ℓ) {x : A} (hx : Comps φA ε aa ℓ x) :
    Comps φA ε aa ℓ (ε * x) := by
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
  obtain ⟨e, he, rfl⟩ := hx
  refine ⟨Fin.cons (ε * e (Fin.last k)) (fun i => e i.castSucc), ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using aa.mul_mem_left ε (he (Fin.last k))
    · simpa using he j.castSucc
  · rw [Fin.sum_univ_castSucc, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, Fin.val_succ, Fin.val_castSucc,
      Fin.val_last, map_mul, hε, pow_zero, one_mul, mul_add, mul_sum]
    rw [add_comm]
    congr 1
    · ring
    · refine sum_congr rfl fun i _ => ?_
      ring
end Formalism.LIFT
