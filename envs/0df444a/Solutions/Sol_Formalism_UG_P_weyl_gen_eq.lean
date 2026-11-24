-- Prove2me | solution 1 for Formalism.UG.P.weyl_gen_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:08:23.454551+00:00
-- url     : https://prove2.me/submissions/30ae3ea7-c536-4995-9096-5e79ebcf95c2

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_LinSubstIsHomogeneous
import Theorems.Thm_Formalism_UG_P_coeff_pow_sum_expand
import Theorems.Thm_Formalism_UG_P_prod_X_pow_fun

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open Formalism Formalism.UG Formalism.UG.P
variable {O : Type} [CommRing O] {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution (α : n →₀ ℕ) (K : ℕ) (hα : α.degree = K) :
    monomial α (α.multinomial : O) =
      coeff α ((∑ j, C (X j) * map C (X j) : MvPolynomial n (MvPolynomial n O)) ^ K) := by
  rw [coeff_pow_sum_expand, Finset.sum_eq_single (⇑α)]
  · have hs : Finsupp.equivFunOnFinite.symm ⇑α = α := Finsupp.equivFunOnFinite.symm_apply_apply α
    rw [prod_X_pow_fun, hs, coeff_monomial, if_pos rfl, C_1, mul_one,
      Finsupp.multinomial_of_support_subset (Finset.subset_univ _),
      ← map_natCast (C : O →+* MvPolynomial n O), C_mul_monomial, mul_one]
  · intro β _ hβ
    rw [prod_X_pow_fun, coeff_monomial, if_neg, C_0, mul_zero]
    intro h
    apply hβ
    rw [← h]
    rfl
  · intro h
    exfalso
    apply h
    rw [Finset.mem_piAntidiag]
    refine ⟨?_, fun i _ => Finset.mem_univ i⟩
    rw [← hα, Finsupp.degree_eq_sum]
end Formalism.UG.P
