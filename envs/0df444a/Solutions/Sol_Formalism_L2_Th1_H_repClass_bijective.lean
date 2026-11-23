-- Prove2me | solution 1 for Formalism.L2.Th1.H.repClass_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:36:51.455497+00:00
-- url     : https://prove2.me/submissions/57b5edeb-c466-46d2-8875-f71a7f37e6f0

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_SemiCharBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_LineTransport
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators ComplexConjugate
namespace Formalism.L2.Th1.H
section Reps
variable {V : Type} [AddCommGroup V] [Module ℂ V]
private theorem quotient_addSubgroupOf_mk_eq_mk_iff_sub_mem {Λ₁ Λ₂ : AddSubgroup V} (a b : Λ₂) :
    (QuotientAddGroup.mk a : Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) = QuotientAddGroup.mk b ↔
      ((b : V) - (a : V)) ∈ Λ₁ := by
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add,
    AddSubgroup.coe_neg, neg_add_eq_sub]
end Reps
end Formalism.L2.Th1.H
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace Formalism.L2.Th1.H
theorem _root_.solution {Λ₁ Λ₂ : AddSubgroup V} {S : Finset V} (hS : IsReps Λ₁ Λ₂ S) :
    Function.Bijective (repClass hS) := by
  constructor
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    have h := (quotient_addSubgroupOf_mk_eq_mk_iff_sub_mem (Λ₁ := Λ₁) (⟨a, hS.1 a ha⟩ : Λ₂) ⟨b, hS.1 b hb⟩).1 hab
    exact Subtype.ext (hS.2.1 b hb a ha h).symm
  · intro c
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientAddGroup.mk_surjective c
    obtain ⟨x, hxS, hyx⟩ := hS.2.2 y hy
    exact ⟨⟨x, hxS⟩, (quotient_addSubgroupOf_mk_eq_mk_iff_sub_mem (Λ₁ := Λ₁) (⟨x, hS.1 x hxS⟩ : Λ₂) ⟨y, hy⟩).2 hyx⟩
end Formalism.L2.Th1.H
