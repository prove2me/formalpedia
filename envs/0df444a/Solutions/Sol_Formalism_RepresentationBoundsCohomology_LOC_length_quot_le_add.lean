-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.LOC.length_quot_le_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:36:45.308667+00:00
-- url     : https://prove2.me/submissions/5575abf7-06ef-4113-9611-221e1f98b647

import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_Statement
import Definitions.Def_Formalism_WachLatticeTwists_TorsionLengthCounts_RowCol
import Definitions.Def_Formalism_WachLatticeTwists_TorsionLengthCounts_SubmoduleLengthBoundStatement
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_LatticeDualProofs_QuotLen
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_LOC_mem_mulSub
import Theorems.Thm_Formalism_NG_IdempotentNormalFormsRhoFacts_length_eq_ker_add_range
import Theorems.Thm_Formalism_NG_IdempotentNormalFormsRhoFacts_length_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open Formalism.NG (KO annih)
noncomputable section
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.LOC
open Module
variable {O : Type u} [CommRing O]
namespace Formalism.RepresentationBoundsCohomology.LOC
theorem _root_.solution (a : O) {M : Type u} [AddCommGroup M] [Module O M]
    (Q : Submodule O M) :
    Module.length O (M ⧸ mulSub a M) ≤
      Module.length O (Q ⧸ mulSub a Q) + Module.length O ((M ⧸ Q) ⧸ mulSub a (M ⧸ Q)) := by
  have hle : mulSub a M ≤ (mulSub a (M ⧸ Q)).comap Q.mkQ := by
    intro x hx
    obtain ⟨m, rfl⟩ := (mem_mulSub x).1 hx
    exact (mem_mulSub _).2 ⟨Q.mkQ m, by rw [map_smul]⟩
  have hle' : mulSub a Q ≤ (mulSub a M).comap Q.subtype := by
    intro x hx
    obtain ⟨m, rfl⟩ := (mem_mulSub x).1 hx
    exact (mem_mulSub _).2 ⟨Q.subtype m, by rw [map_smul]⟩
  let f := Submodule.mapQ (mulSub a M) (mulSub a (M ⧸ Q)) Q.mkQ hle
  let g := Submodule.mapQ (mulSub a Q) (mulSub a M) Q.subtype hle'
  have hker : LinearMap.ker f ≤ LinearMap.range g := by
    intro x hx
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ x
    have h1 : (Submodule.Quotient.mk (Q.mkQ m) : (M ⧸ Q) ⧸ mulSub a (M ⧸ Q)) = 0 := hx
    obtain ⟨w, hw⟩ := (mem_mulSub _).1 ((Submodule.Quotient.mk_eq_zero _).1 h1)
    obtain ⟨m', rfl⟩ := Submodule.mkQ_surjective _ w
    have h2 : m - a • m' ∈ Q := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul]
      rw [sub_eq_zero]
      exact hw.symm
    refine ⟨Submodule.Quotient.mk ⟨m - a • m', h2⟩, ?_⟩
    show (Submodule.Quotient.mk (m - a • m') : M ⧸ mulSub a M) = Submodule.Quotient.mk m
    rw [Submodule.Quotient.eq]
    refine (mem_mulSub _).2 ⟨-m', ?_⟩
    rw [smul_neg]; abel
  calc Module.length O (M ⧸ mulSub a M)
      = Module.length O (LinearMap.ker f) + Module.length O (LinearMap.range f) :=
        Formalism.NG.IdempotentNormalFormsRhoFacts.length_eq_ker_add_range f
    _ ≤ Module.length O (Q ⧸ mulSub a Q) + Module.length O ((M ⧸ Q) ⧸ mulSub a (M ⧸ Q)) := by
        refine add_le_add ?_ ?_
        · exact (Formalism.NG.IdempotentNormalFormsRhoFacts.length_mono hker).trans
            (Module.length_le_of_surjective g.rangeRestrict g.surjective_rangeRestrict)
        · exact Module.length_le_of_injective (LinearMap.range f).subtype
            (Submodule.injective_subtype _)
end Formalism.RepresentationBoundsCohomology.LOC
