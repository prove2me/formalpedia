-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.Dv.sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:22:54.528735+00:00
-- url     : https://prove2.me/submissions/68b1a2b3-835a-4dc7-b992-6f2f768f0022

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AddMulInvMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormRepresentation
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_Dv_add
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_Dv_neg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0
open WA
variable {K : Type*} [Field K] [StarRing K]
variable {S : Subring K} {π : K}
namespace Formalism.HermitianLattices.Ext.L3.U0
namespace Dv
theorem _root_.solution {a b : K} (ha : Dv S π a) (hb : Dv S π b) : Dv S π (a - b) := by
  rw [sub_eq_add_neg]
  exact ha.add hb.neg
end Dv
end Formalism.HermitianLattices.Ext.L3.U0
