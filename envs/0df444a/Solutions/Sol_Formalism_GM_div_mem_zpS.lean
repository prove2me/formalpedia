-- Prove2me | solution 1 for Formalism.GM.div_mem_zpS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:35.631836+00:00
-- url     : https://prove2.me/submissions/5a679d16-d867-4d3b-9aa0-27b50868654d

import Definitions.Def_Formalism_MahlerMeasure_StatementB
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_Mahler

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Polynomial
namespace Formalism.GM
theorem _root_.solution (p k m : ℕ) [hp : Fact p.Prime] (hm1 : 1 ≤ m) (hm : m ≤ p ^ k) :
    ((p : ℚ) ^ k / m) ∈ zpS p := by
  show padicNorm p ((p : ℚ) ^ k / m) ≤ 1
  have hp1 : 1 < p := hp.out.one_lt
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hpk0 : (p : ℚ) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)

  have hv : padicValNat p m ≤ k := by
    have h1 : p ^ padicValNat p m ≤ m := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
    exact (Nat.pow_le_pow_iff_right hp1).1 (h1.trans hm)
  have hval : padicValRat p ((p : ℚ) ^ k / m) = (k : ℤ) - padicValNat p m := by
    rw [padicValRat.div hpk0 hm0, show ((p : ℚ) ^ k) = ((p ^ k : ℕ) : ℚ) by push_cast; rfl,
      padicValRat.of_nat, padicValRat.of_nat, padicValNat.prime_pow]
  rw [padicNorm.eq_zpow_of_nonzero (div_ne_zero hpk0 hm0), hval]
  apply zpow_le_one_of_nonpos₀ (by exact_mod_cast hp1.le)
  omega
end Formalism.GM
