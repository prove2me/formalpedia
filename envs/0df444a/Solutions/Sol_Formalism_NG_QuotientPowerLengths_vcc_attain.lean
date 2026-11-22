-- Prove2me | solution 1 for Formalism.NG.QuotientPowerLengths.vcc_attain
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:22:31.741729+00:00
-- url     : https://prove2.me/submissions/3ebbf1cf-e72f-4ed7-a3f0-7155b73936df

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
variable {X : Type*} {T : Subalgebra O (X → O)} {act : T →+* Module.End (FractionRing O) V}
namespace Formalism.NG.QuotientPowerLengths
theorem _root_.solution (Z : Set X) (x : X) :
    ∃ c ∈ ccIdeal T Z, addVal O ((c : X → O) x) = vcc T Z x := by
  obtain ⟨c, hc⟩ : (⨅ c : ccIdeal T Z, addVal O (((c : T) : X → O) x)) ∈
      Set.range (fun c : ccIdeal T Z => addVal O (((c : T) : X → O) x)) :=
    csInf_mem ⟨_, ⟨0, rfl⟩⟩
  refine ⟨c, c.2, hc.trans ?_⟩
  unfold vcc
  rw [iInf_subtype]
end Formalism.NG.QuotientPowerLengths
