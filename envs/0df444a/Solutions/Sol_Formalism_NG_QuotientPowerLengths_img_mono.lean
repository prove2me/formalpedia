-- Prove2me | solution 1 for Formalism.NG.QuotientPowerLengths.img_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:09:58.960109+00:00
-- url     : https://prove2.me/submissions/d5d3297f-eee2-43bd-b8cb-f05ab9fec056

import Definitions.Def_Formalism_CharacterColumnKernels_StatementN
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LenCokerOfDetNeZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthQuotSmulRangeFree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDiscreteValuationRing
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.QuotientPowerLengths
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {V : Type*} [AddCommGroup V] [Module (FractionRing O) V] [Module O V]
  [IsScalarTower O (FractionRing O) V] [FiniteDimensional (FractionRing O) V]
namespace Formalism.NG.QuotientPowerLengths
theorem _root_.solution {E : Set (Module.End (FractionRing O) V)} {N N' : Submodule O V} (h : N ≤ N') :
    img E N ≤ img E N' := by
  unfold img
  refine Submodule.span_mono ?_
  rintro v ⟨f, hf, n, hn, rfl⟩
  exact ⟨f, hf, n, h hn, rfl⟩
end Formalism.NG.QuotientPowerLengths
