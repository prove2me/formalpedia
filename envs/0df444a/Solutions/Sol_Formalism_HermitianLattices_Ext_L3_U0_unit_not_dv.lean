-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.unit_not_dv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:25:37.77037+00:00
-- url     : https://prove2.me/submissions/af3febfe-e538-4cae-8740-5ae57a958b50

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AddMulInvMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormRepresentation
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_Dv_neg
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_unit_add_dv

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
theorem _root_.solution (hπ : IsUnif S π) {s : K} (hs : IsUnitIn S s) : ¬ Dv S π s := by
  intro h
  have := (unit_add_dv hπ hs h.neg).1
  simp at this
end Formalism.HermitianLattices.Ext.L3.U0
