-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2PrimeSums.gl2a5_count
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:34.298656+00:00
-- url     : https://prove2.me/submissions/242f886b-bd26-4e0f-8160-b0f6d76a389a

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
theorem _root_.solution (N : ℕ) (Y : ℝ) (hY : 0 ≤ Y) :
    ∑ p ∈ Icc 1 N, (if (p : ℝ) ≤ Y then (1 : ℝ) else 0) ≤ Y := by
  rw [Finset.sum_boole]
  have h1 : ((Icc 1 N).filter (fun p : ℕ => (p : ℝ) ≤ Y)).card ≤ (Icc 1 ⌊Y⌋₊).card := by
    apply Finset.card_le_card
    intro p hp
    simp only [mem_filter, mem_Icc] at hp ⊢
    exact ⟨hp.1.1, Nat.le_floor hp.2⟩
  rw [Nat.card_Icc] at h1
  calc ((((Icc 1 N).filter (fun p : ℕ => (p : ℝ) ≤ Y)).card : ℕ) : ℝ) ≤ ((⌊Y⌋₊ + 1 - 1 : ℕ) : ℝ) := by
        exact_mod_cast h1
    _ = (⌊Y⌋₊ : ℝ) := by simp
    _ ≤ Y := Nat.floor_le hY
end Formalism.HermitianLattices.GL2PrimeSums
