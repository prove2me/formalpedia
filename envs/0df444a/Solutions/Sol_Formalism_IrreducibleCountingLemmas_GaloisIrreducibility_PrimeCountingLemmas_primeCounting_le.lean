-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.PrimeCountingLemmas.primeCounting_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:05:58.560795+00:00
-- url     : https://prove2.me/submissions/20e11f54-dc5b-4a67-9999-28631b0918dc

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeRecipSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Nat
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
open Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.PrimeCountingLemmas
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.PrimeCountingLemmas
theorem _root_.solution (s : ℕ) (hs : 6 ≤ s) : (primeCounting s : ℝ) ≤ s / 3 + 3 := by
  have h := Nat.primeCounting_add_le (a := 6) (k := 6) (by norm_num) le_rfl (s - 6)
  have e : 6 + (s - 6) = s := by omega
  rw [e] at h
  have h6 : primeCounting 6 = 3 := by decide
  have t6 : totient 6 = 2 := by decide
  rw [h6, t6] at h
  have h2 : (((s - 6) / 6 : ℕ) : ℝ) ≤ ((s - 6 : ℕ) : ℝ) / 6 := Nat.cast_div_le
  have h3 : ((s - 6 : ℕ) : ℝ) = (s : ℝ) - 6 := by
    rw [Nat.cast_sub hs]; norm_num
  have h4 : (primeCounting s : ℝ) ≤ 3 + 2 * ((((s - 6) / 6 : ℕ) : ℝ) + 1) := by exact_mod_cast h
  rw [h3] at h2
  linarith
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.PrimeCountingLemmas
