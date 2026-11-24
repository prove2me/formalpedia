-- Prove2me | solution 1 for Formalism.BasicNotions.descend_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:38:47.372067+00:00
-- url     : https://prove2.me/submissions/b3e3422c-07aa-4f45-8376-d9b548e1a49f

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_Params
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_LocalRingCardinality_DataCoeff
import Definitions.Def_Formalism_LocalRingCardinality_DataArith
import Definitions.Def_Formalism_LocalRingCardinality_DataKernels
import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Formalism_LocalRingCardinality_DataForms

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions
open NumberField
namespace Formalism.BasicNotions
theorem _root_.solution {K V W M N : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W]
    [Module K W] [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] {σ : K →+* ℂ}
    (e₁ : V →ₛₗ[σ] M) (e₂ : W →ₛₗ[σ] N) (hinj : Function.Injective e₂) (f : M →ₗ[ℂ] N)
    (h : ∀ x, ∃ y, e₂ y = f (e₁ x)) (x : V) : e₂ (descend e₁ e₂ hinj f h x) = f (e₁ x) :=
  Classical.choose_spec (h x)
end Formalism.BasicNotions
