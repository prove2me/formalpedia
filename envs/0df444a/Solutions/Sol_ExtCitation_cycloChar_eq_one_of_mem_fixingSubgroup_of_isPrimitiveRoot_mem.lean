-- Prove2me | solution 1 for ExtCitation.cycloChar_eq_one_of_mem_fixingSubgroup_of_isPrimitiveRoot_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/e238cc34-8490-5da2-86f6-1caf35452a0b

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_cycloChar_eq_one_of_mem_fixingSubgroup_of_isPrimitiveRoot_mem

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation"
open scoped Classical

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
set_option Elab.async false

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation"
open scoped Classical

theorem solution
    {p : ℕ} [Fact p.Prime] (L : IntermediateField ℚ (AlgebraicClosure ℚ))
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p) (hζL : ζ ∈ L)
    (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hs : s ∈ L.fixingSubgroup) :
    cycloChar p s = 1 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hsζ : s ζ = ζ := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hs ζ hζL
  apply Units.ext
  show ((modularCyclotomicCharacter (AlgebraicClosure ℚ) (card_rootsOfUnity_eq_self p)
      (s : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) : (ZMod p)ˣ) : ZMod p) = ((1 : (ZMod p)ˣ) : ZMod p)
  rw [Units.val_one]
  symm
  apply modularCyclotomicCharacter.unique
  intro t ht
  rw [ZMod.val_one, pow_one]
  have htp : ((t : AlgebraicClosure ℚ)) ^ p = 1 := by
    have := (mem_rootsOfUnity p t).1 ht
    rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one htp
  show s (t : AlgebraicClosure ℚ) = t
  rw [← hi, map_pow, hsζ]

end S_ExtCitation_cycloChar_eq_one_of_mem_fixingSubgroup_of_isPrimitiveRoot_mem
end P2MW
export P2MW.S_ExtCitation_cycloChar_eq_one_of_mem_fixingSubgroup_of_isPrimitiveRoot_mem (solution)
