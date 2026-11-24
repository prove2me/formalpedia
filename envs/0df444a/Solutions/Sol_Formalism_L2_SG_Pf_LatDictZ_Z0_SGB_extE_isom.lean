-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z0.SGB.extE_isom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:23:15.767797+00:00
-- url     : https://prove2.me/submissions/9e33801c-6a75-4398-8151-39382f117276

import Mathlib
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_ExistsUnitNorm
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_SelfDualRestr
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_SGB_extE_apply
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_SGB_h_decomp

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
namespace Formalism.L2.SG.Pf.LatDictZ.Z0.SGB
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0) (hs : ∀ u v, star (h u v) = h v u)
    (g : LinearMap.ker (h X) ≃ₗ[K] LinearMap.ker (h X))
    (hg : ∀ u v, h (g u : V) (g v : V) = h (u : V) (v : V)) (x y : V) :
    h (extE h X hX g x) (extE h X hX g y) = h x y := by
  rw [h_decomp h X hX hs, h_decomp h X hX hs x y, extE_apply, extE_apply, coef_ext, coef_ext, proj_ext,
    proj_ext, hg]
end Formalism.L2.SG.Pf.LatDictZ.Z0.SGB
