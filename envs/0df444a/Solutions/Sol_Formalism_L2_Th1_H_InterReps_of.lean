-- Prove2me | solution 1 for Formalism.L2.Th1.H.InterReps_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:40:08.780789+00:00
-- url     : https://prove2.me/submissions/91d28736-67a0-458f-b98a-937af7e1c882

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_SemiCharBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_LineTransport
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
import Theorems.Thm_Formalism_L2_Th1_H_InterClass_of
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
theorem _root_.solution (h : SemiHom) : InterReps := by
  intro V _ _ H hH Λ₁ Λ₂ α hα F hF S hS z
  classical
  have hcl := InterClass_of h V H hH Λ₁ Λ₂ α hα F hF
  letI : Fintype (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) := Fintype.ofBijective _ (repClass_bijective hS)
  unfold inter sumU
  congr 1
  rw [finsum_eq_sum_of_fintype, ← Finset.sum_coe_sort S]
  symm
  refine Fintype.sum_bijective (repClass hS) (repClass_bijective hS) _ _ ?_
  intro s
  show α (s : V) * opU H (s : V) F z = _
  have hmem := sub_quotient_out_mem_of_mk_eq (repClass hS s) ⟨s, hS.1 s s.2⟩ rfl
  have h2 := hcl ((Quotient.out (repClass hS s) : Λ₂) : V) (Quotient.out (repClass hS s)).2
    ((s : V) - ((Quotient.out (repClass hS s) : Λ₂) : V))
    (Λ₂.sub_mem (hS.1 s s.2) (Quotient.out (repClass hS s)).2) hmem z
  rw [show ∀ a b : V, a + (b - a) = b from fun a b => by abel] at h2
  exact h2
end Formalism.L2.Th1.H
