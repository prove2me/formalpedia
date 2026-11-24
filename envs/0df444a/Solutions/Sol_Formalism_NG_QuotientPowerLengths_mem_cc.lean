-- Prove2me | solution 1 for Formalism.NG.QuotientPowerLengths.mem_cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:09:38.765117+00:00
-- url     : https://prove2.me/submissions/4c9dab18-baad-4395-ab3d-5e24a0f16a2b

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
theorem _root_.solution {Z : Set X} {c : T} : c ∈ ccIdeal T Z ↔ ∀ y ∉ Z, (c : X → O) y = 0 := by
  unfold ccIdeal
  rw [RingHom.mem_ker]
  constructor
  · intro h y hy
    exact congrFun h ⟨y, hy⟩
  · intro h
    funext y
    exact h y.1 y.2
end Formalism.NG.QuotientPowerLengths
