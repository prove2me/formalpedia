-- Prove2me | solution 1 for Formalism.HC.ordCompl_mul_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:57:58.277023+00:00
-- url     : https://prove2.me/submissions/453e5107-5d28-40d5-b347-235fb6fe9bae

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostRam

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC
open Formalism.FrobeniusOrbits
namespace Formalism.HC
theorem _root_.solution {m l : ℕ} (hl : l.Prime) (hm : Nat.Coprime m l) : ordCompl[l] (m * l) = m := by
  have hnd : ¬ l ∣ m := (Nat.Prime.coprime_iff_not_dvd hl).mp (Nat.Coprime.symm hm)
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hnd (dvd_zero l)
  have hf : (m * l).factorization l = 1 := by
    rw [Nat.factorization_mul hm0 hl.ne_zero, Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hnd,
      hl.factorization_self, zero_add]
  rw [hf, pow_one, Nat.mul_div_cancel _ hl.pos]
end Formalism.HC
