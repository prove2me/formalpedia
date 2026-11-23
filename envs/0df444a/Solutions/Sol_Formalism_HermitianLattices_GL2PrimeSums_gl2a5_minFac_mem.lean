-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2PrimeSums.gl2a5_minFac_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:29:55.648177+00:00
-- url     : https://prove2.me/submissions/ec2822b0-a9bc-4212-9c3c-eac26058e664

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
theorem _root_.solution {N n : ℕ} (hn : n ∈ primesLeFinset N) : n.minFac ∈ Icc 1 N := by
  simp only [primesLeFinset, mem_filter, mem_Icc] at hn
  rw [mem_Icc]
  exact ⟨(Nat.minFac_pos n), (Nat.minFac_le hn.1.1).trans hn.1.2⟩
end Formalism.HermitianLattices.GL2PrimeSums
