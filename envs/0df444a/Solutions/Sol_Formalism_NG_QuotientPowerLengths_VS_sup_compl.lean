-- Prove2me | solution 1 for Formalism.NG.QuotientPowerLengths.VS_sup_compl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:52.190795+00:00
-- url     : https://prove2.me/submissions/49895406-ccdb-491e-a1c0-4b4d44149e6a

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
theorem _root_.solution (hsum : (⨆ x, Vx T act x) = ⊤) (S : Set X) :
    VS T act S ⊔ VS T act Sᶜ = ⊤ := by
  unfold VS
  rw [eq_top_iff, ← hsum]
  refine iSup_le fun x => ?_
  by_cases hx : x ∈ S
  · exact le_sup_of_le_left (le_iSup₂_of_le x hx le_rfl)
  · exact le_sup_of_le_right (le_iSup₂_of_le x (show x ∈ Sᶜ from hx) le_rfl)
end Formalism.NG.QuotientPowerLengths
