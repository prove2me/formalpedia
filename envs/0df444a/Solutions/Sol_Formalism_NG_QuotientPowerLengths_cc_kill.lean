-- Prove2me | solution 1 for Formalism.NG.QuotientPowerLengths.cc_kill
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:34:10.000899+00:00
-- url     : https://prove2.me/submissions/d423a816-35eb-4a89-9dcf-5a03a37c22b0

import Definitions.Def_Formalism_CharacterColumnKernels_StatementN
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LenCokerOfDetNeZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthQuotSmulRangeFree
import Theorems.Thm_Formalism_NG_QuotientPowerLengths_mem_Vx
import Theorems.Thm_Formalism_NG_QuotientPowerLengths_mem_cc

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
theorem _root_.solution {Z : Set X} {c : T} (hc : c ∈ ccIdeal T Z) :
    VS T act Zᶜ ≤ LinearMap.ker (act c) := by
  unfold VS
  refine iSup₂_le fun y hy => ?_
  intro v hv
  rw [LinearMap.mem_ker, (mem_Vx.mp hv) c, (mem_cc.mp hc) y hy, zero_smul]
end Formalism.NG.QuotientPowerLengths
