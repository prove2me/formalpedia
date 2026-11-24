-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis.totient_odd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:14.843794+00:00
-- url     : https://prove2.me/submissions/7b2acbff-5843-4b7a-b86c-fb400a697f5e

import Definitions.Def_Formalism_FlagUnipotentLattices_IdealCountLeW
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Lemmata_GeneralBFactSecondMore_Imports
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted

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
open Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis
namespace Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis
theorem _root_.solution : ∀ n : ℕ, Odd n → n ≤ Nat.totient n ^ 2 := by
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    intro hodd
    have hp3 : 3 ≤ p := by
      have h2 : p ≠ 2 := by
        rintro rfl
        have : Even (2 ^ k) := (Nat.even_pow.mpr ⟨even_two, hk.ne'⟩)
        exact (Nat.not_odd_iff_even.mpr this) hodd
      have := hp.two_le
      omega
    rw [Nat.totient_prime_pow hp hk]
    obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 3 := ⟨p - 3, by omega⟩
    have h1 : 1 ≤ (q + 3) ^ k := Nat.one_le_pow _ _ (by omega)
    have h2 : (q + 3) ^ k ≤ ((q + 3) ^ k) ^ 2 := by nlinarith
    have h3 : q + 3 ≤ (q + 3 - 1) ^ 2 := by
      have : q + 3 - 1 = q + 2 := by omega
      rw [this]; nlinarith
    calc (q + 3) ^ (k + 1) = (q + 3) ^ k * (q + 3) := pow_succ _ _
      _ ≤ ((q + 3) ^ k) ^ 2 * (q + 3 - 1) ^ 2 := Nat.mul_le_mul h2 h3
      _ = ((q + 3) ^ k * (q + 3 - 1)) ^ 2 := by ring
  | zero => intro _; simp
  | one => intro _; simp
  | coprime a b ha hb hab iha ihb =>
    intro hodd
    rw [Nat.odd_mul] at hodd
    rw [Nat.totient_mul hab, mul_pow]
    exact Nat.mul_le_mul (iha hodd.1) (ihb hodd.2)
end Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis
