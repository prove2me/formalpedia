-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z0.SGB.nondeg_restr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:00:37.724216+00:00
-- url     : https://prove2.me/submissions/ee8d9016-2335-4a10-84a3-00564f55a767

import Mathlib
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_ExistsUnitNorm
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_SelfDualRestr
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_SGB_h_ker_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z0 Formalism.L2.SG.Pf.LatDictZ.Z0.SGB
open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA Formalism.L2.SG.Pf.LatDictZ.Z0.SGA
variable {K : Type} [Field K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V]
variable {S : Subring K}
namespace Formalism.L2.SG.Pf.LatDictZ.Z0.SGB
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : ∀ u v, star (h u v) = h v u)
    (hnd : ∀ x, (∀ y, h x y = 0) → x = 0) {X : V} (hX : h X X ≠ 0) (w : LinearMap.ker (h X))
    (hw : ∀ y, restr h (LinearMap.ker (h X)) w y = 0) : w = 0 := by
  refine Subtype.ext (hnd _ (fun z => ?_))
  rw [decomp h X hX z, map_add, map_smul, smul_eq_mul, h_ker_X h X hs w, mul_zero, zero_add]
  exact hw (proj h X hX z)
end Formalism.L2.SG.Pf.LatDictZ.Z0.SGB
