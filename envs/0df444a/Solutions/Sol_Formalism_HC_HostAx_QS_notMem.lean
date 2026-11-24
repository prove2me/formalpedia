-- Prove2me | solution 1 for Formalism.HC.HostAx.QS_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:59:24.103842+00:00
-- url     : https://prove2.me/submissions/28edccd6-419d-4794-a447-bdc9c421fdcc

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_SmallRam
import Theorems.Thm_Formalism_HC_HostAx_mem_sq_of_dvd_QS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Ideal
noncomputable section
open Formalism Formalism.HC Formalism.HC.HostAx
variable {φ : Frame} (H : HostAx φ)
namespace Formalism.HC.HostAx
theorem _root_.solution (hE : H.toHostRaw.Exact) (P : HeightOneSpectrum (𝓞 H.E)) {p : ℕ} (hp : p.Prime)
    (hc : Nat.card (𝓞 H.E ⧸ P.asIdeal) = p) (h2 : (p : 𝓞 H.E) ∉ P.asIdeal ^ 2) : (H.QS : 𝓞 H.E) ∉ P.asIdeal := by
  have hP := P.isPrime
  have hpm : (p : 𝓞 H.E) ∈ P.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← hc, ← nsmul_one]
    exact card_nsmul_eq_zero'
  intro hm
  by_cases hd : p ∣ H.QS
  · exact h2 (H.mem_sq_of_dvd_QS hE hp hd P.asIdeal hpm)
  · have hcop : IsCoprime ((p : ℕ) : 𝓞 H.E) ((H.QS : ℕ) : 𝓞 H.E) := ((Nat.Prime.coprime_iff_not_dvd hp).2 hd).cast
    obtain ⟨a, b, hab⟩ := hcop
    exact hP.ne_top ((Ideal.eq_top_iff_one _).2 (hab ▸ P.asIdeal.add_mem (P.asIdeal.mul_mem_left a hpm) (P.asIdeal.mul_mem_left b hm)))
end Formalism.HC.HostAx
