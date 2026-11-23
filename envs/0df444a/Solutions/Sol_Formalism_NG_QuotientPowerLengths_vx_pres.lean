-- Prove2me | solution 1 for Formalism.NG.QuotientPowerLengths.vx_pres
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:58.488624+00:00
-- url     : https://prove2.me/submissions/73632502-88c6-4eae-baf7-2f212784cd24

import Definitions.Def_Formalism_CharacterColumnKernels_StatementN
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LenCokerOfDetNeZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthQuotSmulRangeFree
import Theorems.Thm_Formalism_NG_QuotientPowerLengths_mem_Vx

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
theorem _root_.solution (g : Module.End (FractionRing O) V) (hg : ∀ f : T, g * act f = act f * g) (x : X) :
    Vx T act x ≤ (Vx T act x).comap g := by
  intro v hv
  rw [Submodule.mem_comap, mem_Vx]
  rw [mem_Vx] at hv
  intro f
  calc act f (g v) = (act f * g) v := rfl
    _ = (g * act f) v := by rw [hg f]
    _ = g (act f v) := rfl
    _ = g (((f : X → O) x) • v) := by rw [hv f]
    _ = ((f : X → O) x) • g v := by
      rw [← algebraMap_smul (FractionRing O) ((f : X → O) x) v, map_smul, algebraMap_smul]
end Formalism.NG.QuotientPowerLengths
