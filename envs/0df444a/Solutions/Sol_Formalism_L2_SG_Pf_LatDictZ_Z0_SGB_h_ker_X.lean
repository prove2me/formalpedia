-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z0.SGB.h_ker_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:42:29.107661+00:00
-- url     : https://prove2.me/submissions/3fd8379a-10e3-4841-a29b-50a20e131d31

import Mathlib
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_ExistsUnitNorm
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_SelfDualRestr

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
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hs : ∀ u v, star (h u v) = h v u)
    (w : LinearMap.ker (h X)) : h w X = 0 := by
  rw [← hs X w, LinearMap.mem_ker.mp w.2, star_zero]
end Formalism.L2.SG.Pf.LatDictZ.Z0.SGB
