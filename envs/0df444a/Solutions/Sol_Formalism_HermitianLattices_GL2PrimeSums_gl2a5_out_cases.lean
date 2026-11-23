-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2PrimeSums.gl2a5_out_cases
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:34:27.238867+00:00
-- url     : https://prove2.me/submissions/7db40009-e277-4a45-a895-f8a275eb5063

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
theorem _root_.solution (m₀ : ℕ) {n : ℕ} (hn : IsPrimePow n) :
    outPart m₀ n = 1 ∨ outPart m₀ n = n.minFac := by
  obtain ⟨p, k, hp, hk, rfl, hmf, ho⟩ := gl2a5_outPart_primePow m₀ hn
  rw [ho, hmf]
  split_ifs <;> simp
end Formalism.HermitianLattices.GL2PrimeSums
