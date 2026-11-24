-- Prove2me | solution 1 for Formalism.BasicNotions.Host.mem_ramI_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:46:06.997409+00:00
-- url     : https://prove2.me/submissions/f011dfe8-a073-47d7-8cd1-5ba9e8ecff6f

import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_RamDiscr
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_halfSupp
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_CondRd
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_RamEq
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_HalfNorm
import Theorems.Thm_Formalism_BasicNotions_Host_dvd_natAbs_discr_iff
import Theorems.Thm_Formalism_HC_HostRaw_d_not_dvd_QSq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory.HF
open NumberField Ideal
open scoped Pointwise
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Host
variable {R : Ranks} (H : Host R)
namespace Formalism.BasicNotions.Host
theorem _root_.solution {p : ℕ} (hp : p.Prime) : p ∈ H.toHostRaw.ramI ↔ p ∣ H.QS * H.q := by
  have h0 : (discr H.E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero _)
  rw [Formalism.HC.HostRaw.ramI, Finset.mem_erase, Formalism.HC.HostRaw.ram, Nat.mem_primeFactors, H.dvd_natAbs_discr_iff hp]
  constructor
  · rintro ⟨hd, -, h, -⟩
    exact ((Nat.Prime.dvd_mul hp).1 h).resolve_right fun h' =>
      hd ((Nat.prime_dvd_prime_iff_eq hp H.toHostRaw.d_prime).1 h')
  · intro h
    refine ⟨?_, hp, h.mul_right _, h0⟩
    rintro rfl
    exact H.toHostRaw.d_not_dvd_QSq h
end Formalism.BasicNotions.Host
