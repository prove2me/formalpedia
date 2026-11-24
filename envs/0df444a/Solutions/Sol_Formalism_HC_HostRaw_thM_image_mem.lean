-- Prove2me | solution 1 for Formalism.HC.HostRaw.thM_image_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:30:06.076277+00:00
-- url     : https://prove2.me/submissions/63df3a91-18bb-4b14-877a-d470fcf204a0

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycGrp
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_CycImage
import Theorems.Thm_Formalism_HC_HostRaw_image_mem_of_fixed
import Theorems.Thm_Formalism_HC_HostRaw_mem_congrGal_iff
import Theorems.Thm_Formalism_HC_HostRaw_fix_thM_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.HC Formalism.HC.HostRaw
open Formalism.FrobeniusOrbits Formalism.HC.Der
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.HostRaw
theorem _root_.solution {Ω : Type} [Field Ω] [IsAlgClosed Ω] (J : H.E →+* Ω) (M : Subfield Ω) {m : ℕ}
    (hm : m ∣ H.condN) (hM : ∀ y : Ω, y ^ m = 1 → y ∈ M) : J (H.thM m) ∈ M :=
  H.image_mem_of_fixed J M hm hM _ fun u hu =>
    (H.fix_thM_iff m _).2 ((H.mem_congrGal_iff hm _).2 ⟨u, hu, H.gal.apply_symm_apply _⟩)
end Formalism.HC.HostRaw
