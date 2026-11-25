-- Prove2me | solution 1 for Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums.root_of_unity_congruence_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:03:21.570697+00:00
-- url     : https://prove2.me/submissions/fe00d0e8-4c56-4367-b674-1b7b5de24e3b

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_AffineFibreCountComparison
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_InvariantKernelTraceVanishes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.RamifiedLatticeOperators Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums
open Module Finset Matrix
namespace Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums
theorem _root_.solution : Formalism.HermitianLattices.RamifiedLatticeOperators.RootOfUnityCongruenceOne := by
  intro K _ _ P T n b hT hP hTP hn hb hb1 hne
  have hfo : IsOfFinOrder b := isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hb⟩
  have hfin : orderOf b ≠ 0 := (orderOf_pos_iff.mpr hfo).ne'
  have hne1 : orderOf b ≠ 1 := by rwa [Ne, orderOf_eq_one_iff]
  obtain ⟨l, hl, hld⟩ := Nat.exists_prime_and_dvd hne1
  set c := b ^ (orderOf b / l) with hc
  have hco : orderOf c = l := orderOf_pow_orderOf_div hfin hld
  have hpow : ∀ (x : NumberField.RingOfIntegers K) (m : ℕ), x - 1 ∈ P → x ^ m - 1 ∈ P := by
    intro x m hx
    obtain ⟨d, hd⟩ := sub_dvd_pow_sub_pow x 1 m
    rw [one_pow] at hd
    rw [hd]; exact P.mul_mem_right d hx
  have hc1 : c - 1 ∈ P := hpow b _ hb1
  have hcl : c ^ l = 1 := hco ▸ pow_orderOf_eq_one c
  have hcne : c ≠ 1 := by
    intro h; rw [h, orderOf_one] at hco; exact hl.one_lt.ne hco
  have hsum : ∑ i ∈ range l, c ^ i = 0 := by
    have h := mul_geom_sum c l
    rw [hcl, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hcne)
  have hlP : (l : NumberField.RingOfIntegers K) ∈ P := by
    have e : (l : NumberField.RingOfIntegers K) =
        ∑ i ∈ range l, c ^ i - ∑ i ∈ range l, (c ^ i - 1) := by
      simp [Finset.sum_sub_distrib]
    rw [e, hsum, zero_sub]
    exact P.neg_mem (P.sum_mem fun i _ => hpow c i hc1)
  have hlT : l = T := by
    by_contra hlt
    have hcop : IsCoprime (l : ℤ) (T : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hl hT).mpr hlt)
    obtain ⟨x, y, hxy⟩ := hcop
    have h1 : (1 : NumberField.RingOfIntegers K) ∈ P := by
      have e := congrArg (Int.cast : ℤ → NumberField.RingOfIntegers K) hxy
      push_cast at e
      rw [← e]
      exact P.add_mem (P.mul_mem_left _ hlP) (P.mul_mem_left _ hTP)
    exact hP.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  have hprim : IsPrimitiveRoot (algebraMap (NumberField.RingOfIntegers K) K c) T := by
    rw [← hlT, ← hco]
    exact (IsPrimitiveRoot.orderOf c).map_of_injective (IsFractionRing.injective _ K)
  have : NeZero T := ⟨hT.ne_zero⟩
  have hmin := Polynomial.cyclotomic_eq_minpoly_rat hprim (Nat.pos_of_ne_zero hT.ne_zero)
  have hdeg := minpoly.natDegree_le (A := ℚ) (algebraMap (NumberField.RingOfIntegers K) K c)
  rw [← hmin, Polynomial.natDegree_cyclotomic, Nat.totient_prime hT] at hdeg
  exact hdeg
end Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums
