-- Prove2me | solution 1 for Formalism.CyclotomicNorms.jordan_transitivity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:18:53.756386+00:00
-- url     : https://prove2.me/submissions/48e88e50-90a7-444a-b522-6353b3f48def

import Definitions.Def_Formalism_CyclotomicNorms_StatementI
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_Jordan
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_jordanPrime
import Theorems.Thm_Formalism_GaloisIrreducibility_noSolvableTransitive
import Theorems.Thm_Formalism_GaloisIrreducibility_primitiveOfPCycle
import Theorems.Thm_P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_zero
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_zero
attribute [local simp] P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8



set_option autoImplicit false
open Finset
open Formalism Formalism.CyclotomicNorms
namespace Formalism.CyclotomicNorms
theorem _root_.solution : JordanTransitive := by
  intro G Ω _ _ _ _ p g₀ htr hp hlt hle hcyc hsupp
  set K : Subgroup (Equiv.Perm Ω) := (MulAction.toPermHom G Ω).range with hK
  set σ : Equiv.Perm Ω := MulAction.toPerm g₀ with hσ
  have hσK : σ ∈ K := ⟨g₀, rfl⟩
  have htrK : MulAction.IsPretransitive K Ω := by
    constructor
    intro x y
    obtain ⟨g, hg⟩ := htr.exists_smul_eq x y
    exact ⟨⟨MulAction.toPermHom G Ω g, ⟨g, rfl⟩⟩, hg⟩
  have hprim : MulAction.IsPreprimitive K Ω :=
    Formalism.GaloisIrreducibility.primitiveOfPCycle Ω K σ p hp hσK hcyc hsupp hlt htrK
  have halt : alternatingGroup Ω ≤ K :=
    Formalism.GaloisIrreducibility.jordanPrime Ω K σ p hp hσK hcyc hsupp hle hprim
  refine ⟨halt, ?_⟩
  have hpc : p ∈ σ.cycleType := by
    rw [hcyc.cycleType, hsupp]
    simp
  have hns : ¬ Group.IsSolvable K :=
    Formalism.GaloisIrreducibility.noSolvableTransitive Ω K σ p hp hσK hpc hlt hle htrK
  intro hG
  exact hns (Group.isSolvable_of_surjective (MonoidHom.rangeRestrict_surjective (MulAction.toPermHom G Ω)))
end Formalism.CyclotomicNorms
