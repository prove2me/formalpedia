-- Prove2me | solution 1 for Formalism.L2.Th1.H.cosetRepsExist
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:40:08.695875+00:00
-- url     : https://prove2.me/submissions/aa22e3e3-4b0b-4baf-8b36-a399da0844b2

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_SemiCharBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_LineTransport
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
import Theorems.Thm_Formalism_L2_Th1_H_repClass_bijective
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
private theorem quotient_addSubgroupOf_mk_out {Λ₁ Λ₂ : AddSubgroup V} (c : Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) :
    (QuotientAddGroup.mk (Quotient.out c) : Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) = c := by
  exact Quotient.out_eq c
private theorem sub_quotient_out_mem_of_mk_eq {Λ₁ Λ₂ : AddSubgroup V} (c : Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) (y : Λ₂)
    (hc : (QuotientAddGroup.mk y : Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) = c) :
    (y : V) - ((Quotient.out c : Λ₂) : V) ∈ Λ₁ := by
  have h1 : (QuotientAddGroup.mk (Quotient.out c) : Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) =
      QuotientAddGroup.mk y := by
    rw [hc]; exact quotient_addSubgroupOf_mk_out c
  exact (quotient_addSubgroupOf_mk_eq_mk_iff_sub_mem (Λ₁ := Λ₁) (Quotient.out c) y).1 h1
end Reps
end Formalism.L2.Th1.H
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
namespace Formalism.L2.Th1.H
theorem _root_.solution : RepsExist := by
  intro V _ _ Λ₁ Λ₂ hne
  classical
  have hQ : Finite (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) := Nat.finite_of_card_ne_zero hne
  refine ⟨?_, fun S hS => ?_⟩
  · letI : Fintype (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) := Fintype.ofFinite _
    refine ⟨Finset.univ.image (fun c : Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂ => ((Quotient.out c : Λ₂) : V)),
      ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hx
      exact (Quotient.out c).2
    · intro x hx y hy hxy
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨d, -, rfl⟩ := Finset.mem_image.1 hy
      have h1 := (quotient_addSubgroupOf_mk_eq_mk_iff_sub_mem (Λ₁ := Λ₁) (Quotient.out d) (Quotient.out c)).2 hxy
      rw [quotient_addSubgroupOf_mk_out, quotient_addSubgroupOf_mk_out] at h1
      rw [h1]
    · intro y hy
      refine ⟨((Quotient.out (QuotientAddGroup.mk ⟨y, hy⟩ : Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) : Λ₂) : V),
        Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩
      exact sub_quotient_out_mem_of_mk_eq _ ⟨y, hy⟩ rfl
  · have h1 := Nat.card_eq_of_bijective _ (repClass_bijective hS)
    have h2 : Nat.card S = S.card := by
      exact Nat.card_eq_finsetCard S
    rw [h2] at h1
    exact h1
end Formalism.L2.Th1.H
