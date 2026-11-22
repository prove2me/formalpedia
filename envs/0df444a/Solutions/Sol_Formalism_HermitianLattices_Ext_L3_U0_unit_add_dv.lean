-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.unit_add_dv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:37:00.201638+00:00
-- url     : https://prove2.me/submissions/fdb37503-47df-4f07-973f-6c0500374258

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AddMulInvMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormRepresentation
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_unit_mul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_Dv_eq

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
theorem _root_.solution (hπ : IsUnif S π) {s t : K} (hs : IsUnitIn S s) (ht : Dv S π t) :
    IsUnitIn S (s + t) := by
  obtain ⟨r, hr, rfl⟩ := ht.eq hπ
  have : s + π * r = s * (1 + π * (r * s⁻¹)) := by
    have := hs.1
    field_simp
  rw [this]
  exact unit_mul hs (hπ.rad _ (S.mul_mem hr hs.2.2))
end Formalism.HermitianLattices.Ext.L3.U0
