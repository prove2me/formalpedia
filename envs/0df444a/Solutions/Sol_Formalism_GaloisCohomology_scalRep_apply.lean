-- Prove2me | solution 1 for Formalism.GaloisCohomology.scalRep_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:41:40.43467+00:00
-- url     : https://prove2.me/submissions/881b19b3-b91b-4953-ae64-fc08590c30d4

import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_Formalism_GaloisCohomology_Statement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation ReciprocityTheory.Gal Formalism.ConjugateSelfDual
open Formalism Formalism.GaloisCohomology
namespace Formalism.GaloisCohomology
theorem _root_.solution {R : Type*} [CommRing R] {Γ : Type*} [Group Γ] (M : Type*)
    [AddCommGroup M] [Module R M] (ψ : Γ →* Rˣ) (g : Γ) (m : M) :
    scalRep M ψ g m = ((ψ g : Rˣ) : R) • m := rfl
end Formalism.GaloisCohomology
