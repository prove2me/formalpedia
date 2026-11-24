-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z3.hyz_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:02:29.55639+00:00
-- url     : https://prove2.me/submissions/b95a3ebc-753e-427e-899c-f032e5f9e66c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZZLoc

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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z3
open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA Formalism.L2.SG.Pf.LatDictZ.Z0
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {P : Submodule K V} {S : Subring K} {M M₁ M₂ : AddSubgroup V}
namespace Formalism.L2.SG.Pf.LatDictZ.Z3
theorem _root_.solution (hs : h.IsSymm) {z y : V} (hzy : h z y = 1) : h y z = 1 := by
  have e := hs.eq z y
  rw [hzy, map_one] at e
  exact e.symm
end Formalism.L2.SG.Pf.LatDictZ.Z3
