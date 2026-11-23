-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.gcd_prime_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:12.754955+00:00
-- url     : https://prove2.me/submissions/f053bd0c-8f53-4b98-a303-22b7091c1e17

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
theorem _root_.solution {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    ((p : ℤ).gcd (q : ℤ) = 1) ∧ ((q : ℤ).gcd (p : ℤ) = 1) := by
  have h := (Nat.coprime_primes hp hq).mpr hpq.ne
  refine ⟨?_, ?_⟩
  · rw [Int.gcd_natCast_natCast]
    exact h
  · rw [Int.gcd_natCast_natCast]
    exact h.symm
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
