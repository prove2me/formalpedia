-- Prove2me | solution 1 for Formalism.HC.HostRaw.image_mem_of_roots
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:44:27.771003+00:00
-- url     : https://prove2.me/submissions/1a1c6c69-a6ab-4842-9317-f879ce88ee29

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycGrp
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_CycImage
import Theorems.Thm_Formalism_HC_HostRaw_image_mem_of_fixed
import Theorems.Thm_Formalism_HC_HostRaw_art_eq_one_of_modEq

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
theorem _root_.solution {Ω : Type} [Field Ω] [IsAlgClosed Ω] (J : H.E →+* Ω) (M : Subfield Ω)
    (hM : ∀ y : Ω, y ^ H.condN = 1 → y ∈ M) (x : H.E) : J x ∈ M :=
  H.image_mem_of_fixed J M dvd_rfl hM x fun u hu => by rw [H.art_eq_one_of_modEq u hu, map_one]; rfl
end Formalism.HC.HostRaw
