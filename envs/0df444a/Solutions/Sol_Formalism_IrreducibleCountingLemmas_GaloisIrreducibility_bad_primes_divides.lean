-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.bad_primes_divides
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:01:29.675247+00:00
-- url     : https://prove2.me/submissions/4deb2743-63fe-4bf4-8a00-c239bcd4405e

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRBBDivides

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
open Formalism.GaloisIrreducibility (IsSubSum IsOrbit)
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution : BBDivides := by
  intro l g d j Y hl hd hg hY h1 h2 h3
  have hj : j ≤ padicValNat l (g ^ d - 1) := by
    by_contra hlt
    push Not at hlt
    have h5 := h3 _ hlt
    have h4 : g ≤ g ^ d := Nat.le_self_pow (by omega) g
    have h6 : (l : ℝ) ^ (4 * padicValNat l (g ^ d - 1)) ≤ (g : ℝ) := h5.trans hY
    have h7 : l ^ (4 * padicValNat l (g ^ d - 1)) ≤ g := by exact_mod_cast h6
    omega
  exact (pow_dvd_pow l hj).trans pow_padicValNat_dvd
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
