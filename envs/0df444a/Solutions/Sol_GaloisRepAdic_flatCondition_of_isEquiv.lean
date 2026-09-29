-- Prove2me | solution 1 for GaloisRepAdic.flatCondition_of_isEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/fad4949a-fba2-55c7-91a8-b2a3459a46e9

import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_GaloisRepAdic_isFlatAt_of_isEquiv
import Theorems.Thm_GaloisRepAdic_detIsCyclotomic_of_isEquiv
import Theorems.Thm_GaloisRepAdic_isUnramifiedAt_of_isEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_flatCondition_of_isEquiv

theorem solution
    {A : Type} [CommRing A] [IsLocalRing A]
    (𝒪 : Type) [CommRing 𝒪] [Algebra 𝒪 A]
    {ρ₁ ρ₂ : GaloisRepAdic A} (e : ρ₁.IsEquiv ρ₂) {p : ℕ} {S : Finset ℕ}
    (h : GaloisRep.flatCondition 𝒪 p S ρ₁) : GaloisRep.flatCondition 𝒪 p S ρ₂ :=
  ⟨GaloisRepAdic.detIsCyclotomic_of_isEquiv e h.1, GaloisRepAdic.isFlatAt_of_isEquiv e h.2.1,
    fun q hq hqS => GaloisRepAdic.isUnramifiedAt_of_isEquiv e (h.2.2 q hq hqS)⟩

end S_GaloisRepAdic_flatCondition_of_isEquiv
end P2MW
export P2MW.S_GaloisRepAdic_flatCondition_of_isEquiv (solution)
