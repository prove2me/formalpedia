-- Prove2me | solution 1 for Formalism.HC.HostAx.condN_mul_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:03:42.003966+00:00
-- url     : https://prove2.me/submissions/b187eaa6-5c73-4565-bf42-7221b9cd751d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_SmallRam
import Theorems.Thm_Formalism_HC_HostAx_QS_notMem
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
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
theorem _root_.solution (hE : H.toHostRaw.Exact) (P : HeightOneSpectrum (𝓞 H.E)) {p : ℕ} (hp : p.Prime)
    (hc : Nat.card (𝓞 H.E ⧸ P.asIdeal) = p) (h2 : (p : 𝓞 H.E) ∉ P.asIdeal ^ 2) {T : ℕ}
    (h : ((2 * H.q * H.d * T : ℕ) : 𝓞 H.E) ∉ P.asIdeal) : ((H.condN * T : ℕ) : 𝓞 H.E) ∉ P.asIdeal := by
  intro hm
  have e : ((H.condN * T : ℕ) : 𝓞 H.E) = (H.QS : 𝓞 H.E) * ((H.q * H.d * T : ℕ) : 𝓞 H.E) := by
    simp only [HostRaw.condN]; push_cast; ring
  rw [e] at hm
  rcases P.isPrime.mem_or_mem hm with h1 | h1
  · exact H.QS_notMem hE P hp hc h2 h1
  · refine h ?_
    have e' : ((2 * H.q * H.d * T : ℕ) : 𝓞 H.E) = 2 * ((H.q * H.d * T : ℕ) : 𝓞 H.E) := by push_cast; ring
    rw [e']
    exact P.asIdeal.mul_mem_left _ h1
end Formalism.HC.HostAx
