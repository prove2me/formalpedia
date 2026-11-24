-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2PrimeSums.gl2a5_out_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:39.794895+00:00
-- url     : https://prove2.me/submissions/42412862-26ea-4a76-9dcf-dfa3a3f5463c

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SmallPrimeFactorSumBound
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_outPart_primePow

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
theorem _root_.solution (m₀ : ℕ) {n : ℕ} (hn : IsPrimePow n) (h1 : outPart m₀ n = 1) :
    n.minFac ∣ m₀ ∨ ∃ m, n = m ^ 2 := by
  obtain ⟨p, k, hp, hk, rfl, hmf, ho⟩ := gl2a5_outPart_primePow m₀ hn
  rw [hmf]
  rw [ho] at h1
  by_cases hd : p ∣ m₀
  · exact Or.inl hd
  · right
    by_cases hodd : Odd k
    · rw [if_pos ⟨hd, hodd⟩] at h1
      exact absurd h1 hp.one_lt.ne'
    · obtain ⟨j, hj⟩ := Nat.not_odd_iff_even.1 hodd
      exact ⟨p ^ j, by rw [← pow_mul, hj]; congr 1; ring⟩
end Formalism.HermitianLattices.GL2PrimeSums
