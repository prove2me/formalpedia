-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.BQuot.ql_le_of_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:55:35.291376+00:00
-- url     : https://prove2.me/submissions/f8365da1-ddea-49e6-afd2-1a28819873a8

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_ReductionQuotient
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxDet
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_MemSpanBasisFun
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
private theorem len_quot_le_lemma {M Q : Type*} [AddCommGroup M] [Module O M] [AddCommGroup Q]
    [Module O Q] (S : Submodule O M) (φ : M →ₗ[O] Q) (h : LinearMap.ker φ ≤ S) :
    Module.length O (M ⧸ S) ≤ Module.length O Q := by
  refine (Module.length_le_of_surjective (Submodule.factor h) ?_).trans
    (Module.length_le_of_injective ((LinearMap.ker φ).liftQ φ le_rfl) ?_)
  · intro q
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  · rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl
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
theorem _root_.solution {A S : Submodule O V} {L P : Submodule O W} (f : ↥A →ₗ[O] W)
    (h1 : ∀ x, f x ∈ L) (h2 : ∀ x, f x ∈ P → (x : V) ∈ S) : ql A S ≤ ql L P := by
  refine len_quot_le_lemma _ ((P.comap L.subtype).mkQ ∘ₗ f.codRestrict L h1) ?_
  intro x hx
  rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero] at hx
  exact h2 x hx
end Formalism.LatticeBaseChangeAlt.BQuot
