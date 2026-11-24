-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.Pairs.soutPart_mul_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:34:21.519281+00:00
-- url     : https://prove2.me/submissions/ca193612-5e91-4d23-b78e-1577832579a1

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqPairs

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
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.Pairs
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.Pairs
theorem _root_.solution (m₀ a b : ℕ) (h : a.Coprime b) :
    soutPart m₀ (a * b) = soutPart m₀ a * soutPart m₀ b := by
  have hfac := Nat.factorization_mul_of_coprime h
  have hdisj := Nat.Coprime.disjoint_primeFactors h
  unfold soutPart
  rw [Nat.Coprime.primeFactors_mul h, Finset.filter_union,
    Finset.prod_union (Finset.disjoint_filter_filter hdisj)]
  congr 1
  · congr 1
    refine Finset.filter_congr (fun q hq => ?_)
    have hqb : q ∉ b.primeFactors := Finset.disjoint_left.1 hdisj hq
    have h0 : b.factorization q = 0 := by
      by_contra hne
      exact hqb (Nat.support_factorization b ▸ Finsupp.mem_support_iff.2 hne)
    rw [hfac, Finsupp.add_apply, h0, add_zero]
  · congr 1
    refine Finset.filter_congr (fun q hq => ?_)
    have hqa : q ∉ a.primeFactors := Finset.disjoint_right.1 hdisj hq
    have h0 : a.factorization q = 0 := by
      by_contra hne
      exact hqa (Nat.support_factorization a ▸ Finsupp.mem_support_iff.2 hne)
    rw [hfac, Finsupp.add_apply, h0, zero_add]
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.Pairs
