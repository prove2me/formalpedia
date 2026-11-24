-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.PrimeCountingLemmas.S_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:11:45.591504+00:00
-- url     : https://prove2.me/submissions/be95ed6b-f1b2-41ff-a76c-946331cc366c

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeRecipSum
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_PrimeCountingLemmas_ladder_sound
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_PrimeCountingLemmas_factorial_ladder_thirteen
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_PrimeCountingLemmas_factorial_ladder_thirty_one
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_PrimeCountingLemmas_factorial_ladder_one_forty_one

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
theorem _root_.solution (N : ℕ) (h1 : 100 ≤ N) (h2 : N < 20000) : (1 : ℝ) / 20 ≤ S N := by
  by_cases h3 : N < 196
  · exact ladder_sound (by norm_num) rfl 60 100 factorial_ladder_thirteen N h1 h3
  by_cases h4 : N < 1024
  · exact ladder_sound (by norm_num) rfl 60 196 factorial_ladder_thirty_one N (by omega) h4
  · exact ladder_sound (by norm_num) rfl 60 1024 factorial_ladder_one_forty_one N (by omega) h2
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.PrimeCountingLemmas
