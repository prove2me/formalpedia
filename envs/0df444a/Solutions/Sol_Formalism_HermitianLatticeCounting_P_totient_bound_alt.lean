-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.totient_bound_alt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:49:04.954731+00:00
-- url     : https://prove2.me/submissions/8dcf19ed-0f7a-4d83-aa85-a0f2ebe33499

import Definitions.Def_Formalism_FlagUnipotentLattices_IdealCountLeW
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Lemmata_GeneralBFactSecondMore_Imports
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_DualLatticeIndexBis_totient_odd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open NumberField
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : TotientBound := by
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn.ne'
  have hcop : Nat.Coprime (2 ^ k) m := Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hm)
  have h1 := DualLatticeIndexBis.totient_odd m hm
  rw [Nat.totient_mul hcop, mul_pow]
  have h2 : 2 ^ k ≤ 2 * Nat.totient (2 ^ k) ^ 2 := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · rw [Nat.totient_prime_pow Nat.prime_two hk]
      obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      have h1 : 1 ≤ 2 ^ k := Nat.one_le_pow _ _ (by omega)
      rw [pow_succ]
      nlinarith
  calc 2 ^ k * m ≤ (2 * Nat.totient (2 ^ k) ^ 2) * Nat.totient m ^ 2 := Nat.mul_le_mul h2 h1
    _ = 2 * (Nat.totient (2 ^ k) ^ 2 * Nat.totient m ^ 2) := by ring
end Formalism.HermitianLatticeCounting.P
