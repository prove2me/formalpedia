-- Prove2me | solution 1 for Formalism.HC.Der.zO_sub_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:50:17.827639+00:00
-- url     : https://prove2.me/submissions/6cc624ef-3d38-4248-9d6a-bc90c4927b19

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycLift
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RootEqOfSubMem
import Theorems.Thm_Formalism_HC_Der_root_eq_of_sub_mem
import Theorems.Thm_Formalism_HC_Der_zO_prim
import Theorems.Thm_Formalism_HC_Der_charP_quot

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
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable (N : ℕ) [NeZero N]
variable (l : ℕ) [Fact l.Prime] (Q : Ideal (𝓞 (Cond.Cyc N))) [Q.IsPrime] [Q.LiesOver (span {(l : ℤ)})]
namespace Formalism.HC.Der
theorem _root_.solution (a b : ℕ) : zO N ^ a - zO N ^ b ∈ Q ↔ a ≡ b [MOD ordCompl[l] N] := by
  haveI := charP_quot N l Q
  have hl : l.Prime := Fact.out
  have hN0 : N ≠ 0 := NeZero.ne N
  have hnN : ordProj[l] N * ordCompl[l] N = N := Nat.ordProj_mul_ordCompl_eq_self N l
  have hN'0 : 0 < ordCompl[l] N := Nat.ordCompl_pos l hN0
  have hζ := zO_prim N
  have key1 : ∀ c, Ideal.Quotient.mk Q (zO N ^ (ordCompl[l] N * c)) = 1 := by
    intro c
    have h1 : (Ideal.Quotient.mk Q (zO N ^ (ordCompl[l] N * c)) - 1) ^ (ordProj[l] N) = 0 := by
      rw [sub_pow_char_pow, ← map_pow, ← pow_mul, one_pow,
        show ordCompl[l] N * c * l ^ N.factorization l = N * c by
          rw [mul_right_comm, mul_comm (ordCompl[l] N), hnN],
        pow_mul, hζ.pow_eq_one, one_pow, map_one, sub_self]
    exact sub_eq_zero.1 ((pow_eq_zero_iff (pow_ne_zero _ hl.ne_zero)).1 h1)
  rw [← Ideal.Quotient.eq]
  constructor
  · intro h
    have h1 : (zO N ^ (ordProj[l] N)) ^ a = (zO N ^ (ordProj[l] N)) ^ b := by
      apply root_eq_of_sub_mem Q (m := ordCompl[l] N)
      · intro hmem
        have h2 : ((ordCompl[l] N : ℕ) : 𝓞 (Cond.Cyc N) ⧸ Q) = 0 := by
          rw [← map_natCast (Ideal.Quotient.mk Q), Ideal.Quotient.eq_zero_iff_mem]
          exact hmem
        rw [CharP.cast_eq_zero_iff _ l] at h2
        exact Nat.not_dvd_ordCompl hl hN0 h2
      · have ex : ordProj[l] N * (a * ordCompl[l] N) = N * a := by
          rw [mul_left_comm, hnN, mul_comm]
        rw [← pow_mul, ← pow_mul, ex, pow_mul, hζ.pow_eq_one, one_pow]
      · have ex : ordProj[l] N * (b * ordCompl[l] N) = N * b := by
          rw [mul_left_comm, hnN, mul_comm]
        rw [← pow_mul, ← pow_mul, ex, pow_mul, hζ.pow_eq_one, one_pow]
      · rw [← Ideal.Quotient.eq]
        have e1 : (zO N ^ (ordProj[l] N)) ^ a = (zO N ^ a) ^ (ordProj[l] N) := by
          rw [← pow_mul, ← pow_mul, mul_comm]
        have e2 : (zO N ^ (ordProj[l] N)) ^ b = (zO N ^ b) ^ (ordProj[l] N) := by
          rw [← pow_mul, ← pow_mul, mul_comm]
        rw [e1, e2, map_pow (Ideal.Quotient.mk Q) (zO N ^ a), map_pow (Ideal.Quotient.mk Q) (zO N ^ b), h]
    have hprim : IsPrimitiveRoot (zO N ^ (ordProj[l] N)) (ordCompl[l] N) :=
      hζ.pow_of_dvd (pow_ne_zero _ hl.ne_zero) (Nat.ordProj_dvd N l)
    have e : ∀ c, (zO N ^ (ordProj[l] N)) ^ c = (zO N ^ (ordProj[l] N)) ^ (c % ordCompl[l] N) := fun c => by
      conv_lhs => rw [← Nat.mod_add_div c (ordCompl[l] N), pow_add, pow_mul, hprim.pow_eq_one, one_pow, mul_one]
    rw [e a, e b] at h1
    exact hprim.pow_inj (Nat.mod_lt _ hN'0) (Nat.mod_lt _ hN'0) h1
  · intro h
    rcases le_total b a with hab | hab
    · obtain ⟨c, hc⟩ : ordCompl[l] N ∣ a - b := (Nat.modEq_iff_dvd' hab).1 h.symm
      have hac : a = b + ordCompl[l] N * c := by omega
      rw [hac, pow_add, map_mul, key1, mul_one]
    · obtain ⟨c, hc⟩ : ordCompl[l] N ∣ b - a := (Nat.modEq_iff_dvd' hab).1 h
      have hbc : b = a + ordCompl[l] N * c := by omega
      rw [hbc, pow_add, map_mul, key1, mul_one]
end Formalism.HC.Der
