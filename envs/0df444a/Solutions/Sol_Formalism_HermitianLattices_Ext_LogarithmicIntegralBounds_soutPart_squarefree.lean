-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.soutPart_squarefree
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:06:36.450161+00:00
-- url     : https://prove2.me/submissions/699817ba-e453-43f2-9114-617b99c2e8a5

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqJac

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
theorem _root_.solution (m₀ N : ℕ) : Squarefree (soutPart m₀ N) := by
  unfold soutPart
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp r hr hpr => ?_) fun p hp =>
    (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).squarefree
  simp only [← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
    (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hr).1)).mpr hpr
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
