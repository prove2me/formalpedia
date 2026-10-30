-- Prove2me | solution 1 for DerivativeChainDivisorAnchor.power_pair_drop
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T21:24:54.616282+00:00
-- url     : https://prove2.me/submissions/46ee053f-6e7a-4424-86e9-b4f65e24c35c

import Mathlib
import Definitions.Def_DerivativeChainGini_DivisorAnchorFunctional
import Definitions.Def_DerivativeChainGini_PairDropPolynomialPower
import Definitions.Def_DerivativeChainGini_PairDropSignedEnergy
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainDivisorAnchor
end DerivativeChainDivisorAnchor
namespace DerivativeChainGini
end DerivativeChainGini
namespace DerivativeChainGiniCircle
end DerivativeChainGiniCircle
namespace DerivativeChainGiniFamily
end DerivativeChainGiniFamily
namespace DerivativeChainPrivate
end DerivativeChainPrivate


set_option autoImplicit false
open scoped BigOperators
open Polynomial DerivativeChainGiniFamily
namespace DerivativeChainDivisorAnchor
noncomputable section



theorem multiset_sum_coe (s : Multiset ℂ) (f : ℂ → ℝ) :
    (s.map f).sum = ∑ i : s, f (i:ℂ) := by
  symm
  change ((Finset.univ : Finset s).val.map (fun i : s => f (i:ℂ))).sum = _
  rw [Multiset.map_univ]

theorem multisetPair_coe (s t : Multiset ℂ) :
    multisetPair s t = ∑ i : s, ∑ j : t, ‖(i:ℂ)-(j:ℂ)‖ := by
  unfold multisetPair
  simp_rw [multiset_sum_coe]

theorem multisetPair_symm (s t : Multiset ℂ) : multisetPair s t = multisetPair t s := by
  rw [multisetPair_coe, multisetPair_coe, Finset.sum_comm]
  simp_rw [norm_sub_rev]

theorem multisetPair_add_left (s t u : Multiset ℂ) :
    multisetPair (s+t) u = multisetPair s u+multisetPair t u := by
  simp only [multisetPair, Multiset.map_add, Multiset.sum_add]

theorem multisetPair_add_right (s t u : Multiset ℂ) :
    multisetPair s (t+u) = multisetPair s t+multisetPair s u := by
  simp only [multisetPair, Multiset.map_add, Multiset.sum_add, Multiset.sum_map_add]

theorem multisetPair_nsmul_left (s t : Multiset ℂ) (r : ℕ) :
    multisetPair (r • s) t = (r:ℝ)*multisetPair s t := by
  simp only [multisetPair, Multiset.map_nsmul, Multiset.sum_nsmul, nsmul_eq_mul]

theorem multisetPair_nsmul_right (s t : Multiset ℂ) (r : ℕ) :
    multisetPair s (r • t) = (r:ℝ)*multisetPair s t := by
  rw [multisetPair_symm, multisetPair_nsmul_left, multisetPair_symm t s]



























end
end DerivativeChainDivisorAnchor


set_option autoImplicit false
open scoped BigOperators
open Polynomial DerivativeChainGiniFamily
namespace DerivativeChainDivisorAnchor
noncomputable section













theorem power_source_roots (P : ℂ[X]) (r : ℕ) : (powerSource P r).roots = r • P.roots := by
  simp only [powerSource, roots_pow]

theorem power_child_roots (P Q : ℂ[X]) (hP : P.Monic) (hQ : Q.Monic) (r : ℕ) :
    (powerChild P Q r).roots = (r-1) • P.roots+Q.roots := by
  rw [powerChild, roots_mul (mul_ne_zero (pow_ne_zero _ hP.ne_zero) hQ.ne_zero), roots_pow]















end
end DerivativeChainDivisorAnchor


set_option autoImplicit false
open scoped BigOperators
open Polynomial DerivativeChainGiniFamily
open DerivativeChainDivisorAnchor




















theorem solution (P Q : ℂ[X]) (hP : P.Monic) (hQ : Q.Monic)
    (hn : 0 < P.natDegree) (r : ℕ) (hr : 1 ≤ r) :
    pairDrop (powerSource P r) (powerChild P Q r) =
      (r:ℝ)*(P.natDegree:ℝ)*rootAnchor P Q+divisorEnergy P Q := by
  have hnR : (P.natDegree:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  change multisetPair (powerSource P r).roots (powerSource P r).roots/2-
      multisetPair (powerChild P Q r).roots (powerChild P Q r).roots/2 = _
  rw [power_source_roots, power_child_roots P Q hP hQ r]
  simp only [multisetPair_add_left, multisetPair_add_right, multisetPair_nsmul_left, multisetPair_nsmul_right]
  rw [multisetPair_symm Q.roots P.roots]
  change _ = (r:ℝ)*(P.natDegree:ℝ)*((multisetPair P.roots P.roots-multisetPair P.roots Q.roots)/(P.natDegree:ℝ))+
    (multisetPair P.roots Q.roots-multisetPair P.roots P.roots/2-multisetPair Q.roots Q.roots/2)
  rw [Nat.cast_sub hr]
  push_cast
  field_simp
  <;> ring
