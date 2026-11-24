-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2PrimeSums.gl2a5_outPart_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:39.530825+00:00
-- url     : https://prove2.me/submissions/0c1941cf-ed77-4b0c-80fd-1bce55b41623

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SmallPrimeFactorSumBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GL2PrimeSums
namespace Formalism.HermitianLattices.GL2PrimeSums
theorem _root_.solution (m₀ : ℕ) {m m' : ℕ} (h : Nat.Coprime m m') :
    outPart m₀ (m * m') = outPart m₀ m * outPart m₀ m' := by
  unfold outPart
  rw [h.primeFactors_mul, Finset.filter_union,
    Finset.prod_union (Finset.disjoint_filter_filter h.disjoint_primeFactors)]
  congr 1
  · apply Finset.prod_congr _ (fun _ _ => rfl)
    apply Finset.filter_congr
    intro p hp
    have h0 : m'.factorization p = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hd
      exact (Finset.disjoint_left.1 h.disjoint_primeFactors hp)
        (Nat.mem_primeFactors.2 ⟨(Nat.mem_primeFactors.1 hp).1, hd, by
          rintro rfl
          have := (Nat.coprime_zero_right m).1 h
          subst this
          simp at hp⟩)
    rw [Nat.factorization_mul_of_coprime h]
    simp [h0]
  · apply Finset.prod_congr _ (fun _ _ => rfl)
    apply Finset.filter_congr
    intro p hp
    have h0 : m.factorization p = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hd
      exact (Finset.disjoint_right.1 h.disjoint_primeFactors hp)
        (Nat.mem_primeFactors.2 ⟨(Nat.mem_primeFactors.1 hp).1, hd, by
          rintro rfl
          have := (Nat.coprime_zero_left m').1 h
          subst this
          simp at hp⟩)
    rw [Nat.factorization_mul_of_coprime h]
    simp [h0]
end Formalism.HermitianLattices.GL2PrimeSums
