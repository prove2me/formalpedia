-- Prove2me | solution 1 for Formalism.L2.DIV.finite_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:35:54.727367+00:00
-- url     : https://prove2.me/submissions/d30b3670-295b-4e83-a7c1-ef70e2ea9e18

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ConjugationAtDistinguishedPlace
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_PowValCast
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoeffLemmas
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_HC_HostRaw_jOf_coe
import Theorems.Thm_Formalism_L2_Host_algC_coe
import Theorems.Thm_Formalism_L2_Host_jOf_coe
import Theorems.Thm_Formalism_L2_Host_restr_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.HC.HostRaw.jOf_coe
attribute [local simp] Formalism.L2.Host.algC_coe
attribute [local simp] Formalism.L2.Host.jOf_coe
attribute [local simp] Formalism.L2.Host.restr_apply



set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.L2.Host Formalism.DivisionValues
namespace Formalism.L2.DIV
theorem _root_.solution {n : ℕ} (hn : 0 < n) (a : Qb) : {z : Qb | z ^ n = a}.Finite := by
  classical
  refine (Polynomial.nthRoots n a).toFinset.finite_toSet.subset fun z hz => ?_
  simpa [Polynomial.mem_nthRoots hn] using hz
end Formalism.L2.DIV
