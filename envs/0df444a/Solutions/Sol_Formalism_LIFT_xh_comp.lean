-- Prove2me | solution 1 for Formalism.LIFT.xh_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:43:06.983797+00:00
-- url     : https://prove2.me/submissions/471a95ae-a555-4e25-8660-4c850656882b

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_CompsOfMemMap
import Theorems.Thm_Formalism_LIFT_comp_mem

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
theorem _root_.solution (hℓ : 0 < ℓ) (hε : φA ε = ε ^ ℓ)
    (hU : ∀ g : A, ∃! e : Fin ℓ → A, g = ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (e i))
    (X Q : A) (H : ℕ) (hX : φA X = X * Q)
    (hQ : ∀ a ∈ aa, Q ^ H * a ∈ Ideal.map φA aa) (e : Fin ℓ → A)
    (h : X ^ H * ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (e i) ∈ aa) (i : Fin ℓ) :
    X ^ H * e i ∈ aa := by
  have h1 := hQ _ h
  have h2 : Q ^ H * (X ^ H * ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (e i)) =
      ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (X ^ H * e i) := by
    simp only [map_mul, map_pow, hX, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    ring
  exact comp_mem φA ε aa hℓ hε hU h1 (fun i => X ^ H * e i) h2 i
end Formalism.LIFT
