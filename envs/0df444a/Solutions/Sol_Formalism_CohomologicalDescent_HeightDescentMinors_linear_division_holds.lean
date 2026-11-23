-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.linear_division_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:43:26.75683+00:00
-- url     : https://prove2.me/submissions/014ae663-e44f-4c58-b235-2b02cf496056

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_X_sub_C_isDistinguished
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_coe_X_sub_C_polynomial_powerSeries
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_order_X_sub_C_mod_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution : LinDivision := by
  intro O _ _ I _ c hc
  have H := (X_sub_C_isDistinguished I c hc).isWeierstrassDivisorAt'
  constructor
  · intro f
    obtain ⟨hd, he⟩ := H.isWeierstrassDivisionAt_div_mod f
    rw [order_X_sub_C_mod_eq_one I c hc] at hd
    generalize H.div f = qq at he
    generalize H.mod f = rr at he hd
    have hC : rr = Polynomial.C (rr.coeff 0) :=
      Polynomial.eq_C_of_degree_le_zero (Nat.WithBot.lt_one_iff_le_zero.mp (by simpa using hd))
    refine ⟨qq, rr.coeff 0, ?_⟩
    rw [coe_X_sub_C_polynomial_powerSeries, hC, Polynomial.coe_C] at he
    simpa using he
  · intro f₁ f₂ a₁ a₂ h
    have hdeg : ∀ a : O, (Polynomial.C a : Polynomial O).degree <
        ((((Polynomial.X - Polynomial.C c : Polynomial O) : O⟦X⟧).map
          (Ideal.Quotient.mk I)).order.toNat : WithBot ℕ) := fun a => by
      rw [order_X_sub_C_mod_eq_one I c hc]
      exact lt_of_le_of_lt Polynomial.degree_C_le (by simp)
    have := H.eq_of_mul_add_eq_mul_add (q := f₁) (q' := f₂) (hdeg a₁) (hdeg a₂)
      (by rw [coe_X_sub_C_polynomial_powerSeries, Polynomial.coe_C, Polynomial.coe_C]; exact h)
    exact ⟨this.1, Polynomial.C_injective this.2⟩
end Formalism.CohomologicalDescent.HeightDescentMinors
