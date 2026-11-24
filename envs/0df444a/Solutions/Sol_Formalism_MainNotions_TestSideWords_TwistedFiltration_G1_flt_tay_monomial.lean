-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_tay_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:33:26.293201+00:00
-- url     : https://prove2.me/submissions/acc7d34c-0a37-43cc-8a3f-03bf33467cbc

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_AlmostEverywhereSpherical
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_SumCCMulSumOfMulEqOne
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_g_pascal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.TestSideWords Formalism.MainNotions.TestSideWords.TwistedFiltration Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
open Formalism.MainNotions.G
namespace Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
theorem _root_.solution (R : Type*) [CommRing R] {σ : Type*} (m : σ →₀ ℕ) :
    ∀ be, coeff be (flt_tay R σ (monomial m 1)) = flt_g R m be := by
  classical
  have htx : ∀ a, flt_tay R σ (X a) = C (X a) + X a := fun a => by simp [flt_tay]
  have step : ∀ m : σ →₀ ℕ, (∀ be, coeff be (flt_tay R σ (monomial m 1)) = flt_g R m be) →
      ∀ a be, coeff be (flt_tay R σ (monomial (m + Finsupp.single a 1) 1)) =
        flt_g R (m + Finsupp.single a 1) be := by
    intro m hm a be
    rw [flt_g_pascal, monomial_add_single, pow_one, map_mul, htx, mul_add, coeff_add,
      mul_comm _ (C (X a)), coeff_C_mul, coeff_mul_X', hm, mul_comm (X a)]
    by_cases ha : a ∈ be.support
    · simp [ha, hm]
    · simp [ha]
  induction m using Finsupp.induction with
  | zero =>
    intro be
    by_cases hbe : be = 0
    · subst hbe
      simp [flt_g]
    · obtain ⟨k, hk⟩ : ∃ k, be k ≠ 0 := by
        by_contra hc
        push_neg at hc
        exact hbe (Finsupp.ext hc)
      have hz : (be.prod fun k j => ((Nat.choose 0 j : ℕ) : R)) = 0 := by
        rw [Finsupp.prod]
        exact Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hk)
          (by rw [Nat.choose_eq_zero_of_lt (by omega)]; simp)
      simp [flt_g, hz, coeff_one, Ne.symm hbe]
  | single_add a b f _ hb ih =>
    clear hb
    induction b with
    | zero => simpa using ih
    | succ b ihb =>
      have e : Finsupp.single a (b + 1) + f = (Finsupp.single a b + f) + Finsupp.single a 1 := by
        rw [Finsupp.single_add, add_right_comm]
      rw [e]
      exact step _ ihb a
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
