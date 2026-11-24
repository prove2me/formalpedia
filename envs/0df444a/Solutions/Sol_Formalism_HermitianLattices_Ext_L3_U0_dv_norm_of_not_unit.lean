-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.dv_norm_of_not_unit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:46:36.565527+00:00
-- url     : https://prove2.me/submissions/2c656098-5dd9-4619-82ad-14ad9876c498

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AddMulInvMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormRepresentation
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_isUnitIn_of_mul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_dv_of_not_unit
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_star_norm

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
theorem _root_.solution (hS : IsHermSemilocal S) (hπ : IsUnif S π) {a : K} (ha : a ∈ S)
    (hn : ¬ IsUnitIn S a) : Dv S π (star a * a) :=
  dv_of_not_unit hπ (S.mul_mem (hS.star_mem _ ha) ha) (star_norm a)
    fun h => hn (isUnitIn_of_mul (hS.star_mem _ ha) ha h)
end Formalism.HermitianLattices.Ext.L3.U0
