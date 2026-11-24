-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z0.SGB.h_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:00:36.130665+00:00
-- url     : https://prove2.me/submissions/51c63b63-16df-4c38-bfa2-5e20a88f0cb3

import Mathlib
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_ExistsUnitNorm
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_SelfDualRestr
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_SGB_h_ker_X
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open NumberField
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z0 Formalism.L2.SG.Pf.LatDictZ.Z0.SGB
open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA Formalism.L2.SG.Pf.LatDictZ.Z0.SGA
variable {K : Type} [Field K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V]
namespace Formalism.L2.SG.Pf.LatDictZ.Z0.SGB
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0) (hs : ∀ u v, star (h u v) = h v u)
    (x y : V) :
    h x y = star (coef h X x) * coef h X y * h X X + h (proj h X hX x) (proj h X hX y) := by
  conv_lhs => rw [decomp h X hX x, decomp h X hX y]
  simp only [LinearMap.map_add₂, map_add, LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul, starRingEnd_apply,
    LinearMap.add_apply, LinearMap.smul_apply]
  rw [LinearMap.mem_ker.mp (proj h X hX y).2, h_ker_X h X hs (proj h X hX x)]
  ring
end Formalism.L2.SG.Pf.LatDictZ.Z0.SGB
