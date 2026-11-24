-- Prove2me | solution 1 for Formalism.HC.Der.kc_no_root_d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:14:50.005753+00:00
-- url     : https://prove2.me/submissions/4836eff3-1542-4efc-9db9-8867819a95af

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcBase
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcEqOfPowEqOne
import Theorems.Thm_Formalism_FrobeniusOrbits_Mu_mu_card_le_two
import Theorems.Thm_Formalism_FrobeniusOrbits_Mu_mu_le_ram
import Theorems.Thm_Formalism_FrobeniusOrbits_Mu_mu_mem_pow
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_card


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise nonZeroDivisors
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {φ : Frame} (H : HostRaw φ)
variable (C : HostCore H)
include C
namespace Formalism.HC.Der
theorem _root_.solution (η : H.E) (hη : IsPrimitiveRoot η H.d) : False := by
  have : Fact H.d.Prime := ⟨H.hyp.2.1⟩
  have := H.galois
  obtain ⟨⟨Q, hQp, hQl⟩⟩ : Nonempty ((span {(H.d : ℤ)}).primesOver (𝓞 H.E)) := inferInstance
  have hge := Mu.mu_le_ram H.d Q (H.d - 1) (Mu.mu_mem_pow H.d Q η hη)
  have hd := H.hyp.2.2.2.1
  have hle := Mu.mu_card_le_two (L := H.E) H.gal H.gal.injective φ.iod (Q.inertia Gal(H.E/ℚ))
    (fun ρ hρ => (C.inertia_d Q ρ).mp (AddSubgroup.mem_inertia.mp hρ))
  rw [odd_card H.E H.d Q] at hle
  omega
end Formalism.HC.Der
