-- Prove2me | solution 1 for GaloisRepAdic.strictOrdinaryCondition_baseChangeAlong
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/b217b09f-ea60-5ba2-a594-ba003965ea83

import Mathlib
import Definitions.Def_GaloisRep_StrictOrdinary
import Theorems.Thm_GaloisRepAdic_isStrictOrdinaryAt_baseChangeAlong
import Theorems.Thm_GaloisRepAdic_detIsCyclotomic_baseChangeAlong
import Theorems.Thm_GaloisRepAdic_isUnramifiedAt_baseChangeAlong
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_strictOrdinaryCondition_baseChangeAlong

set_option autoImplicit false

theorem solution
    {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (𝒪 : Type) [CommRing 𝒪] [Algebra 𝒪 A] [Algebra 𝒪 B]
    (φ : A →+* B) (hφ : IsLocalHom φ) (ρ : GaloisRepAdic A) {p : ℕ} {S : Finset ℕ}
    (h : GaloisRep.strictOrdinaryCondition 𝒪 p S ρ) :
    GaloisRep.strictOrdinaryCondition 𝒪 p S (ρ.baseChangeAlong φ hφ) :=
  ⟨GaloisRepAdic.detIsCyclotomic_baseChangeAlong φ hφ ρ h.1,
    GaloisRepAdic.isStrictOrdinaryAt_baseChangeAlong φ hφ ρ h.2.1,
    fun q hq hqS => GaloisRepAdic.isUnramifiedAt_baseChangeAlong φ hφ ρ (h.2.2 q hq hqS)⟩

end S_GaloisRepAdic_strictOrdinaryCondition_baseChangeAlong
end P2MW
export P2MW.S_GaloisRepAdic_strictOrdinaryCondition_baseChangeAlong (solution)
