-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.BQuot.ql_triangle
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:41:16.840009+00:00
-- url     : https://prove2.me/submissions/c6dce917-a7e4-4565-a8ba-a47e7ee3f1f6

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_ReductionQuotient
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxDet
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_MemSpanBasisFun
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_BQuot_ql_le_of_map
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.LatticeBaseChangeAlt
open Module
namespace BQuot
section General
variable {O V W : Type*} [CommRing O] [AddCommGroup V] [Module O V] [AddCommGroup W] [Module O W]
private theorem len_quot_tri_lemma_2 {M : Type*} [AddCommGroup M] [Module O M] (P Q : Submodule O M) :
    Module.length O (M ⧸ Q) ≤ Module.length O (M ⧸ P) + Module.length O (↥P ⧸ Q.comap P.subtype) := by
  set N : Submodule O (M ⧸ Q) := LinearMap.range (Q.mkQ ∘ₗ P.subtype) with hN
  rw [Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
    (LinearMap.exact_subtype_mkQ N), add_comm]
  gcongr
  · refine Module.length_le_of_surjective
      (P.liftQ (N.mkQ ∘ₗ Q.mkQ) ?_) ?_
    · intro x hx
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      exact ⟨⟨x, hx⟩, rfl⟩
    · intro q
      obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      exact ⟨Submodule.Quotient.mk m, rfl⟩
  · refine Module.length_le_of_surjective
      ((Q.comap P.subtype).liftQ (Q.mkQ ∘ₗ P.subtype).rangeRestrict ?_) ?_
    · intro x hx
      rw [LinearMap.mem_ker]
      apply Subtype.ext
      simp only [LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.subtype_apply, ZeroMemClass.coe_zero, LinearMap.rangeRestrict,
        Submodule.Quotient.mk_eq_zero]
      exact hx
    · intro q
      obtain ⟨x, hx⟩ := LinearMap.surjective_rangeRestrict (Q.mkQ ∘ₗ P.subtype) q
      exact ⟨Submodule.Quotient.mk x, hx⟩
end General
section DVR
variable {O K V : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V]
  [IsScalarTower O K V]
end DVR
end BQuot
end Formalism.LatticeBaseChangeAlt
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeBaseChangeAlt
open Module
open Formalism.LatticeBaseChangeAlt.BQuot
variable {O V W : Type*} [CommRing O] [AddCommGroup V] [Module O V] [AddCommGroup W] [Module O W]
namespace Formalism.LatticeBaseChangeAlt.BQuot
theorem _root_.solution (A B C : Submodule O V) : ql A C ≤ ql A B + ql B C := by
  refine (len_quot_tri_lemma_2 (B.comap A.subtype) (C.comap A.subtype)).trans ?_
  gcongr
  exact ql_le_of_map (V := ↥A) (A := B.comap A.subtype) (S := C.comap A.subtype)
    (A.subtype ∘ₗ (B.comap A.subtype).subtype) (fun x => x.2) (fun _ hx => hx)
end Formalism.LatticeBaseChangeAlt.BQuot
