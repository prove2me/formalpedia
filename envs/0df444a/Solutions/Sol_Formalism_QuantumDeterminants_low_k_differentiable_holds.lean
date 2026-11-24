-- Prove2me | solution 1 for Formalism.QuantumDeterminants.low_k_differentiable_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:38:51.672093+00:00
-- url     : https://prove2.me/submissions/0aaab2d5-171b-4ea5-a132-1315d0f5acd1

import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_HalfSumRootsStandard
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_DSLowK
import Theorems.Thm_Formalism_QuantumDeterminants_dslowk_lowK_eq
import Theorems.Thm_Formalism_QuantumDeterminants_dslowk_counts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.REAL
namespace Formalism.QuantumDeterminants
theorem _root_.solution : LowKDiff := by
  intro n ε lam a b hab he
  obtain ⟨h1, h2, h3⟩ := dslowk_counts ε hab he
  rw [dslowk_lowK_eq, dslowk_lowK_eq]
  unfold rhoC
  have r1 := congrArg (Nat.cast (R := ℝ)) h1
  have r2 := congrArg (Nat.cast (R := ℝ)) h2
  have r3 := congrArg (Nat.cast (R := ℝ)) h3
  push_cast at r1 r2 r3
  linarith
end Formalism.QuantumDeterminants
