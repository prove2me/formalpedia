-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.BasisReduction.len_comap_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:33:54.164615+00:00
-- url     : https://prove2.me/submissions/73b35efd-1923-44d4-b31d-a1d2f71cd98f

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_ReductionQuotient
import Definitions.Def_Formalism_LogFactorialIndices_LogProductFormula
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_ReductionQuotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeBaseChangeAlt
open Module
open Formalism.LatticeBaseChangeAlt.BasisReduction
open Formalism.LatticeIndexTer.subgroupData
variable {O X : Type} [CommRing O] [AddCommGroup X] [Module O X]
namespace Formalism.LatticeBaseChangeAlt.BasisReduction
theorem _root_.solution {M M' : Type} [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']
    (f : M →ₗ[O] M') (p : Submodule O M') :
    Module.length O (M ⧸ p.comap f) ≤ Module.length O (M' ⧸ p) := by
  apply Module.length_le_of_injective (Submodule.mapQ (p.comap f) p f le_rfl)
  intro x y hxy
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  simp only [Submodule.mapQ_apply] at hxy
  rw [Submodule.Quotient.eq] at hxy ⊢
  simpa using hxy
end Formalism.LatticeBaseChangeAlt.BasisReduction
