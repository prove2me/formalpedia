-- Prove2me | solution 1 for Formalism.NG.QuotientPowerLengths.cc_mem_VS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:43:09.173426+00:00
-- url     : https://prove2.me/submissions/ba280420-4c21-4b87-a155-c28709fa3916

import Definitions.Def_Formalism_CharacterColumnKernels_StatementN
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LenCokerOfDetNeZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthQuotSmulRangeFree
import Theorems.Thm_Formalism_NG_QuotientPowerLengths_vx_pres
import Theorems.Thm_Formalism_NG_QuotientPowerLengths_VS_pres
import Theorems.Thm_Formalism_NG_QuotientPowerLengths_VS_sup_compl
import Theorems.Thm_Formalism_NG_QuotientPowerLengths_cc_kill
import Theorems.Thm_Formalism_NG_QuotientPowerLengths_cc_comm

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
theorem _root_.solution (hsum : (⨆ x, Vx T act x) = ⊤) {Z : Set X} {c : T} (hc : c ∈ ccIdeal T Z)
    (v : V) : act c v ∈ VS T act Z := by
  have hv : v ∈ VS T act Z ⊔ VS T act Zᶜ := by
    rw [VS_sup_compl hsum Z]
    exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
  have hpres := VS_pres (act c) (fun y => vx_pres (act c) (fun f => cc_comm c f) y) Z
  rw [map_add, LinearMap.mem_ker.mp (cc_kill hc hb), add_zero]
  exact hpres ha
end Formalism.NG.QuotientPowerLengths
