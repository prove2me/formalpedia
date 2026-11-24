-- Prove2me | solution 1 for Formalism.MainNotions.DIV.HookProducts.RBTie.mem_dualLat_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:39:01.853934+00:00
-- url     : https://prove2.me/submissions/5793ab2f-8fe7-4434-904f-8eda265c7161

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_LocalRingCardinality_DataArith
import Definitions.Def_Formalism_SharpRestriction_Divisibility_HookProducts_RBTieOp
import Definitions.Def_Formalism_SharpRestriction_Divisibility_HookProducts_RBTieSlope
import Definitions.Def_Formalism_SharpRestriction_Divisibility_HookProducts_RBTieMu

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField Module
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.DIV Formalism.MainNotions.DIV.HookProducts Formalism.MainNotions.DIV.HookProducts.RBTie
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.MainNotions.DIV.HookProducts.RBTie
theorem _root_.solution {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (A : Submodule (𝓞 K) V) (f : Module.Dual K V) :
    f ∈ Formalism.HN.dualLat A ↔ ∀ x ∈ A, f x ∈ Set.range (algebraMap (𝓞 K) K) := Iff.rfl
end Formalism.MainNotions.DIV.HookProducts.RBTie
