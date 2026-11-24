-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.hostProG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:59:06.194712+00:00
-- url     : https://prove2.me/submissions/c5c1454d-6a06-4ced-96f3-83edd4c4d796

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ExistsOpenNormalOrderOf
import Theorems.Thm_Formalism_FrobeniusOrbits_Stab_exists_open_normal_orderOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.FrobeniusOrbits
theorem _root_.solution : HostProG := by
  intro g hg G _ _ _ _ _ hN x hx
  obtain ⟨N, hNx⟩ := Stab.exists_open_normal_orderOf x hx
  obtain ⟨m, hm⟩ := hN N.toSubgroup N.toOpenSubgroup.isOpen inferInstance
  have hdvd : orderOf x ∣ g ^ m := by
    rw [← hNx, ← hm]
    exact orderOf_dvd_natCard _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hg).1 hdvd
  exact ⟨j, hj⟩
end Formalism.FrobeniusOrbits
