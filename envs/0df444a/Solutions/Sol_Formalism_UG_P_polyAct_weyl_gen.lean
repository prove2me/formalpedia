-- Prove2me | solution 1 for Formalism.UG.P.polyAct_weyl_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:24:39.746815+00:00
-- url     : https://prove2.me/submissions/de03af9d-af96-47de-90e8-5c722e703fb2

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_LinSubstIsHomogeneous
import Theorems.Thm_Formalism_UG_P_coeff_pow_sum_expand
import Theorems.Thm_Formalism_UG_P_prod_X_pow_fun
import Theorems.Thm_Formalism_UG_P_weyl_gen_eq
import Theorems.Thm_Formalism_UG_P_map_polyAct_pow

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
theorem _root_.solution (g : GL n O) (K : ℕ) (α : n →₀ ℕ) (hα : α.degree = K) :
    polyAct O n g (monomial α (α.multinomial : O)) ∈ weylSub O n K := by
  rw [weyl_gen_eq α K hα]
  have h1 : polyAct O n g
      (coeff α ((∑ j, C (X j) * map C (X j) : MvPolynomial n (MvPolynomial n O)) ^ K))
      = coeff α (map (polyAct O n g).toRingHom
          ((∑ j, C (X j) * map C (X j) : MvPolynomial n (MvPolynomial n O)) ^ K)) :=
    (coeff_map _ _ _).symm
  rw [h1, map_polyAct_pow, coeff_pow_sum_expand]
  refine Submodule.sum_mem _ (fun β hβ => ?_)
  have hdeg : (Finsupp.equivFunOnFinite.symm β).degree = K := by
    rw [Finsupp.degree_eq_sum]
    exact (Finset.mem_piAntidiag.mp hβ).1
  have hm : Nat.multinomial Finset.univ β = (Finsupp.equivFunOnFinite.symm β).multinomial :=
    Finsupp.multinomial_of_support_subset (s := Finset.univ)
      (d := Finsupp.equivFunOnFinite.symm β) (Finset.subset_univ _)
  rw [prod_X_pow_fun, hm]
  generalize coeff (R := O) (σ := n) α _ = c
  have he : ((Finsupp.equivFunOnFinite.symm β).multinomial : MvPolynomial n O) *
      monomial (Finsupp.equivFunOnFinite.symm β) 1 * C c
      = c • monomial (Finsupp.equivFunOnFinite.symm β)
          ((Finsupp.equivFunOnFinite.symm β).multinomial : O) := by
    rw [smul_eq_C_mul, ← map_natCast (C : O →+* MvPolynomial n O), C_mul_monomial, mul_one,
      mul_comm]
  rw [he]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hdeg, rfl⟩)
end Formalism.UG.P
