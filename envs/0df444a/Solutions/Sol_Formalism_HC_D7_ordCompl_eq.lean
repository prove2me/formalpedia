-- Prove2me | solution 1 for Formalism.HC.D7.ordCompl_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:45:03.139817+00:00
-- url     : https://prove2.me/submissions/7d44e47f-8e42-498e-b7cb-b087bea8da95

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSym
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSymOfModEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC Formalism.HC.D7
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.HC.D7
theorem _root_.solution {l m : ℕ} (hl : l.Prime) (k : ℕ) (hm : ¬ l ∣ m) : ordCompl[l] (l ^ k * m) = m := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero l)
  have hf : (l ^ k * m).factorization l = k := by
    rw [Nat.factorization_mul (pow_ne_zero _ hl.ne_zero) hm0, Finsupp.add_apply,
      hl.factorization_pow, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hm, add_zero]
  rw [hf, Nat.mul_div_cancel_left _ (pow_pos hl.pos _)]
end Formalism.HC.D7
