-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.ld_coeff_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:55:24.364603+00:00
-- url     : https://prove2.me/submissions/9af2c75f-c376-44b3-9252-f9b5f9c50ec2

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
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
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution {S : Type*} [CommRing S] (a b c : S) (m k : ℕ) :
    ((Polynomial.C a + Polynomial.X * Polynomial.C b) ^ m * Polynomial.C c).coeff k =
      (m.choose k : S) * a ^ (m - k) * b ^ k * c := by
  rw [Polynomial.coeff_mul_C]
  congr 1
  rw [add_comm (Polynomial.C a), add_pow, Polynomial.finset_sum_coeff]
  have hterm : ∀ j ∈ Finset.range (m + 1),
      ((Polynomial.X * Polynomial.C b) ^ j * Polynomial.C a ^ (m - j) * (m.choose j : Polynomial S)).coeff k =
        if k = j then (m.choose j : S) * a ^ (m - j) * b ^ j else 0 := by
    intro j _
    rw [show (Polynomial.X * Polynomial.C b) ^ j * Polynomial.C a ^ (m - j) * (m.choose j : Polynomial S) =
        Polynomial.C (b ^ j * a ^ (m - j) * (m.choose j : S)) * Polynomial.X ^ j by
      simp only [mul_pow, map_mul, map_pow, map_natCast]; ring]
    rw [Polynomial.coeff_C_mul_X_pow]
    split_ifs with hkj
    · subst hkj; ring
    · rfl
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq]
  split_ifs with hk
  · rfl
  · rw [Finset.mem_range] at hk
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp
end Formalism.CohomologicalDescent.LD
