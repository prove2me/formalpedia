-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.jacobi_class_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:35.243747+00:00
-- url     : https://prove2.me/submissions/609a7785-3ae2-4887-805c-88b3b7e61954

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqJac
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_gcd_prime_lt
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_jacobi_prime_in
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_jacobi_prime_out
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_jacobi_class_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
theorem _root_.solution {m₀ N q q' : ℕ} (h8 : 8 ∣ m₀) (hN : 0 < N) (hq : q.Prime) (hq' : q'.Prime)
    (hqq : q % m₀ = q' % m₀) (hNq : N < q) (hNq' : N < q') :
    jacobiSym (N : ℤ) q * jacobiSym (q : ℤ) (soutPart m₀ N) =
      jacobiSym (N : ℤ) q' * jacobiSym (q' : ℤ) (soutPart m₀ N) := by
  rw [jacobi_class_prod m₀ N q hN, jacobi_class_prod m₀ N q' hN]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hpP := Nat.prime_of_mem_primeFactors hp
  have hpN : p ≤ N := Nat.le_of_mem_primeFactors hp
  have hpq : p < q := by omega
  have hpq' : p < q' := by omega
  by_cases hpm : p ∣ m₀
  · rw [if_neg (fun h => h.2 hpm), if_neg (fun h => h.2 hpm), mul_one, mul_one,
      jacobi_prime_in h8 hpP hpm hq hq' hqq hpq hpq']
  · have hsq : ∀ r : ℕ, r.Prime → p < r → jacobiSym (p : ℤ) r ^ 2 = 1 := fun r hr hpr =>
      jacobiSym.sq_one (gcd_prime_lt hpP hr hpr).1
    obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' (N.factorization p)
    · have hnodd : ¬ Odd (N.factorization p) := Nat.not_odd_iff_even.mpr ⟨k, by omega⟩
      rw [if_neg (fun h => hnodd h.1), if_neg (fun h => hnodd h.1), mul_one, mul_one, hk, pow_mul, pow_mul,
        hsq q hq hpq, hsq q' hq' hpq', one_pow]
    · have hodd : Odd (N.factorization p) := ⟨k, hk⟩
      rw [if_pos ⟨hodd, hpm⟩, if_pos ⟨hodd, hpm⟩, hk, pow_succ, pow_succ, pow_mul, pow_mul,
        hsq q hq hpq, hsq q' hq' hpq', one_pow, one_mul, one_mul]
      exact jacobi_prime_out h8 hpP hpm hq hq' hqq hpq hpq'
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
