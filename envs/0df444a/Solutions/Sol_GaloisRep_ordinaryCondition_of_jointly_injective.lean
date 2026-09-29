-- Prove2me | solution 1 for GaloisRep.ordinaryCondition_of_jointly_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/c9fb7a26-be37-5298-bae6-d9026b02aa39

import Definitions.Def_GaloisRep_LocalConditions
import Theorems.Thm_GaloisRepAdic_detIsCyclotomic_of_jointly_injective
import Theorems.Thm_GaloisRepAdic_isOrdinaryAt_of_jointly_injective
import Theorems.Thm_GaloisRepAdic_isUnramifiedAt_of_jointly_injective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_ordinaryCondition_of_jointly_injective

theorem solution
    {P A B : Type} [CommRing P] [IsLocalRing P] [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B]
    (𝒪 : Type) [CommRing 𝒪] [Algebra 𝒪 P] [Algebra 𝒪 A] [Algebra 𝒪 B]
    (πA : P →+* A) (hπA : IsLocalHom πA) (πB : P →+* B) (hπB : IsLocalHom πB)
    (hinj : ∀ x, πA x = 0 → πB x = 0 → x = 0) (ρ : GaloisRepAdic P) {p : ℕ} {S : Finset ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hnA : IsNilpotent (p : A)) (hnB : IsNilpotent (p : B))
    (hA : GaloisRep.ordinaryCondition 𝒪 p S (ρ.baseChangeAlong πA hπA))
    (hB : GaloisRep.ordinaryCondition 𝒪 p S (ρ.baseChangeAlong πB hπB)) :
    GaloisRep.ordinaryCondition 𝒪 p S ρ := by
  obtain ⟨hA₁, hA₂, hA₃⟩ := hA
  obtain ⟨hB₁, hB₂, hB₃⟩ := hB
  exact ⟨GaloisRepAdic.detIsCyclotomic_of_jointly_injective πA hπA πB hπB hinj ρ hnA hnB hA₁ hB₁,
    GaloisRepAdic.isOrdinaryAt_of_jointly_injective πA hπA πB hπB hinj ρ hp hp2 hA₁ hA₂ hB₂,
    fun q hq hqS => GaloisRepAdic.isUnramifiedAt_of_jointly_injective πA hπA πB hπB hinj ρ
      (hA₃ q hq hqS) (hB₃ q hq hqS)⟩

end S_GaloisRep_ordinaryCondition_of_jointly_injective
end P2MW
export P2MW.S_GaloisRep_ordinaryCondition_of_jointly_injective (solution)
