-- Prove2me | solution 1 for GaloisRepAdic.flatCondition_of_jointly_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/d1948cd4-a034-59f1-89e6-f90965787512

import Mathlib.RingTheory.Artinian.Ring
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_GaloisRepAdic_detIsCyclotomic_of_jointly_injective
import Theorems.Thm_GaloisRepAdic_isFlatAt_of_jointly_injective
import Theorems.Thm_GaloisRepAdic_isUnramifiedAt_of_jointly_injective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_flatCondition_of_jointly_injective
p2m_attr_erase "instance" "instIsScalarTowerTensorProduct_definitions"
p2m_attr_erase "simp" "closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff"

namespace Beta7

theorem isNilpotent_of_mem_maximalIdeal {B : Type} [CommRing B] [IsLocalRing B]
    [IsArtinianRing B] {x : B} (hx : x ∈ IsLocalRing.maximalIdeal B) : IsNilpotent x := by
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := B)
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hn
  refine ⟨n, ?_⟩
  have h := Ideal.pow_mem_pow hx n
  rw [hn, Ideal.zero_eq_bot] at h
  exact Ideal.mem_bot.mp h

end Beta7

theorem solution
    {P A B : Type} [CommRing P] [IsLocalRing P] [CommRing A] [IsLocalRing A] [IsArtinianRing A]
    [CommRing B] [IsLocalRing B] [IsArtinianRing B]
    (𝒪 : Type) [CommRing 𝒪] [Algebra 𝒪 P] [Algebra 𝒪 A] [Algebra 𝒪 B]
    (πA : P →+* A) (hπA : IsLocalHom πA) (πB : P →+* B) (hπB : IsLocalHom πB)
    (hinj : ∀ x, πA x = 0 → πB x = 0 → x = 0) (ρ : GaloisRepAdic P) {p : ℕ} {S : Finset ℕ}
    (hA : GaloisRep.flatCondition 𝒪 p S (ρ.baseChangeAlong πA hπA))
    (hB : GaloisRep.flatCondition 𝒪 p S (ρ.baseChangeAlong πB hπB)) :
    GaloisRep.flatCondition 𝒪 p S ρ := by
  refine ⟨?_, ?_, ?_⟩
  · exact GaloisRepAdic.detIsCyclotomic_of_jointly_injective πA hπA πB hπB hinj ρ
      (Beta7.isNilpotent_of_mem_maximalIdeal hA.1.1) (Beta7.isNilpotent_of_mem_maximalIdeal hB.1.1)
      hA.1 hB.1
  · exact GaloisRepAdic.isFlatAt_of_jointly_injective πA hπA πB hπB hinj ρ hA.2.1 hB.2.1
  · exact fun q hq hqS => GaloisRepAdic.isUnramifiedAt_of_jointly_injective πA hπA πB hπB hinj ρ
      (hA.2.2 q hq hqS) (hB.2.2 q hq hqS)

#print axioms solution

end S_GaloisRepAdic_flatCondition_of_jointly_injective
end P2MW
export P2MW.S_GaloisRepAdic_flatCondition_of_jointly_injective (solution)
