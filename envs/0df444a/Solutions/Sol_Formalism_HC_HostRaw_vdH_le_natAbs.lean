-- Prove2me | solution 1 for Formalism.HC.HostRaw.vdH_le_natAbs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:58:32.01344+00:00
-- url     : https://prove2.me/submissions/7763e0e8-fb5f-4bc2-b508-ff7d88af0e76

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_SlopeTestRemainingChoices
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_VdHLeNatAbs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.HC.HostRaw
theorem _root_.solution {φ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ) (p : ℕ) :
    H.vdH p ≤ ((NumberField.discr H.E).natAbs : ℝ) := by
  unfold Formalism.HC.HostRaw.vdH
  have h1 : (1 : ℝ) ≤ (Module.finrank ℚ H.E : ℝ) := by exact_mod_cast Module.finrank_pos
  have h2 : padicValNat p (NumberField.discr H.E).natAbs ≤ (NumberField.discr H.E).natAbs :=
    (padicValNat_le_nat_log _).trans (Nat.log_le_self _ _)
  have h3 : (padicValNat p (NumberField.discr H.E).natAbs : ℝ) ≤ ((NumberField.discr H.E).natAbs : ℝ) := by exact_mod_cast h2
  exact (div_le_self (Nat.cast_nonneg _) h1).trans h3
end Formalism.HC.HostRaw
