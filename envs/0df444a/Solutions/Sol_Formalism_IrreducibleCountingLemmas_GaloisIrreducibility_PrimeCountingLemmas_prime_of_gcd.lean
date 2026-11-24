-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.PrimeCountingLemmas.prime_of_gcd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:01:21.061679+00:00
-- url     : https://prove2.me/submissions/8fdd2e7c-90b7-4ee9-8597-ef6ad76620a2

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
theorem _root_.solution {r p : ℕ} (h1 : r < p) (h2 : p < (r + 1) * (r + 1))
    (h3 : Nat.gcd p (r.factorial) = 1) : p.Prime := by
  have hp2 : 2 ≤ p := by
    rcases Nat.lt_or_ge r 1 with hr | hr
    · nlinarith
    · omega
  by_contra hnp
  have hq := Nat.minFac_prime (by omega : p ≠ 1)
  have hqd : p.minFac ∣ p := Nat.minFac_dvd p
  have hqr : r < p.minFac := by
    by_contra hle
    push_neg at hle
    have h4 : p.minFac ∣ r.factorial := Nat.dvd_factorial hq.pos hle
    have h5 : p.minFac ∣ Nat.gcd p r.factorial := Nat.dvd_gcd hqd h4
    rw [h3] at h5
    exact hq.one_lt.ne' (Nat.dvd_one.1 h5)
  have hsq := Nat.minFac_sq_le_self (by omega) hnp
  nlinarith
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.PrimeCountingLemmas
