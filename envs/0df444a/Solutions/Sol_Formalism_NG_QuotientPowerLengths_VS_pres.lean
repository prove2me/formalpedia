-- Prove2me | solution 1 for Formalism.NG.QuotientPowerLengths.VS_pres
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:51.913883+00:00
-- url     : https://prove2.me/submissions/c9dff1c7-ee55-4c71-9e6e-dc5e383a23e2

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
theorem _root_.solution (g : Module.End (FractionRing O) V) (hg : ∀ y, Vx T act y ≤ (Vx T act y).comap g)
    (S : Set X) : VS T act S ≤ (VS T act S).comap g := by
  unfold VS
  exact iSup₂_le fun y hy => (hg y).trans (Submodule.comap_mono (le_iSup₂_of_le y hy le_rfl))
end Formalism.NG.QuotientPowerLengths
