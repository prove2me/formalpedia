-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.PrimeCountingLemmas.ladder_sound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:59:40.999312+00:00
-- url     : https://prove2.me/submissions/e42abc4a-1cd2-4008-8020-786e2d42aca6

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeRecipSum
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_PrimeCountingLemmas_chk_sound

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
theorem _root_.solution {M F r T : ℕ} (hM : 0 < M) (hF : F = r.factorial) :
    ∀ (f a : ℕ), ladder M F r T f a = true →
    ∀ N, a ≤ N → N < T → (1 : ℝ) / 20 ≤ S N := by
  intro f
  induction f with
  | zero =>
    intro a h N h1 h2
    simp only [ladder, Nat.ble_eq] at h
    omega
  | succ f ih =>
    intro a h N h1 h2
    simp only [ladder, Bool.or_eq_true, Nat.ble_eq, Bool.and_eq_true] at h
    rcases h with h | ⟨h3, h4⟩
    · omega
    · by_cases hN : N ≤ a + a / 10
      · exact chk_sound hM hF h3 N h1 hN
      · exact ih _ h4 N (by omega) h2
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.PrimeCountingLemmas
