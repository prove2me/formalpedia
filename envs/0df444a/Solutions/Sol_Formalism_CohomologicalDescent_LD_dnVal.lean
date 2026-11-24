-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.dnVal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:20:04.538336+00:00
-- url     : https://prove2.me/submissions/23db63a0-fc1a-4328-a42a-f5fcf3560c19

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Theorems.Thm_Formalism_CohomologicalDescent_LD_dnDvd
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution : DnVal := by
  intro l p w i q m lam2 hl hb
  have : Fact l.Prime := ⟨hl⟩
  have hdvd := dnDvd p w i q m lam2 hb
  have h1 : (l : ℤ) ^ padicValInt l (Dn p w i lam2) ∣ (((w + q - m - 1).factorial ^ p : ℕ) : ℤ) :=
    dvd_trans (padicValInt_dvd _) hdvd
  have hF : (((w + q - m - 1).factorial ^ p : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast pow_ne_zero p (Nat.factorial_ne_zero _)
  have h2 : padicValInt l (Dn p w i lam2) ≤ padicValInt l (((w + q - m - 1).factorial ^ p : ℕ) : ℤ) := by
    rcases (padicValInt_dvd_iff _ _).mp h1 with h | h
    · exact absurd h hF
    · exact h
  rw [padicValInt.of_nat, padicValNat.pow] at h2
  have h3 := sub_one_mul_padicValNat_factorial (p := l) (w + q - m - 1)
  calc (l - 1) * padicValInt l (Dn p w i lam2)
      ≤ (l - 1) * (p * padicValNat l (w + q - m - 1).factorial) := Nat.mul_le_mul_left _ h2
    _ = p * ((l - 1) * padicValNat l (w + q - m - 1).factorial) := by ring
    _ ≤ p * (w + q - m - 1) := Nat.mul_le_mul_left _ (by rw [h3]; exact Nat.sub_le _ _)
end Formalism.CohomologicalDescent.LD
