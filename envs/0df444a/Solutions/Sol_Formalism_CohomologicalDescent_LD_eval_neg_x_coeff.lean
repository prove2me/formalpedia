-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.eval_neg_x_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:08:30.140555+00:00
-- url     : https://prove2.me/submissions/58021ccc-a3de-4aab-9215-eda96afac387

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LA
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution {S : Type*} [CommRing S] (φ : S →+* S) (p : Polynomial S) (k : ℕ) :
    (Polynomial.eval₂ (Polynomial.C.comp φ) (-Polynomial.X) p).coeff k = (-1) ^ k * φ (p.coeff k) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.eval₂_add, Polynomial.coeff_add, Polynomial.coeff_add, hp, hq, map_add, mul_add]
  | monomial n a =>
    rw [Polynomial.eval₂_monomial, RingHom.comp_apply, Polynomial.coeff_C_mul, neg_pow, Polynomial.coeff_monomial,
      ← Polynomial.C_1, ← Polynomial.C_neg, ← Polynomial.C_pow, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases h : n = k
    · subst h
      simp
      ring
    · simp [h, Ne.symm h]
end Formalism.CohomologicalDescent.LD
