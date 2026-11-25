-- Prove2me | solution 1 for Formalism.HC.HostAx.two_mul_notMem_of_condN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:58:23.214358+00:00
-- url     : https://prove2.me/submissions/52cc5726-2b3c-40c5-bad5-af980424ca9c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_SmallRam
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_HC_HostRaw_two_dvd_QS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open NumberField IsDedekindDomain Ideal
noncomputable section
open Formalism Formalism.HC Formalism.HC.HostAx
variable {φ : Frame} (H : HostAx φ)
namespace Formalism.HC.HostAx
theorem _root_.solution (P : HeightOneSpectrum (𝓞 H.E)) {T : ℕ}
    (h : ((H.condN * T : ℕ) : 𝓞 H.E) ∉ P.asIdeal) : ((2 * H.q * H.d * T : ℕ) : 𝓞 H.E) ∉ P.asIdeal := by
  intro hm
  obtain ⟨c, hc⟩ := H.two_dvd_QS
  refine h ?_
  have e : ((H.condN * T : ℕ) : 𝓞 H.E) = (c : 𝓞 H.E) * ((2 * H.q * H.d * T : ℕ) : 𝓞 H.E) := by
    simp only [HostRaw.condN]; rw [hc]; push_cast; ring
  rw [e]
  exact P.asIdeal.mul_mem_left _ hm
end Formalism.HC.HostAx
