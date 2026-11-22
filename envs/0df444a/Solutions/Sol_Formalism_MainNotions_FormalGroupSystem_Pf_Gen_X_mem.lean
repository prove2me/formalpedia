-- Prove2me | solution 1 for Formalism.MainNotions.FormalGroupSystem.Pf.Gen.X_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:03:21.157801+00:00
-- url     : https://prove2.me/submissions/ef53d249-06a4-4698-9c39-82b8911fbc45

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MultisetValuation_CoeffProdRename
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MultisetValuation_JpSubstExpand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.FormalGroupSystem.Pf Formalism.MainNotions.FormalGroupSystem.Pf.Gen
open Finset
variable {R σ Pl : Type} [CommRing R]
namespace Formalism.MainNotions.FormalGroupSystem.Pf.Gen
theorem _root_.solution {π : σ → Pl} {v : Pl} {x : σ} (h : π x = v) : (MvPowerSeries.X x : MvPowerSeries σ R) ∈ SuppOn π v := by
  classical
  intro m hm y hy
  rw [MvPowerSeries.coeff_X] at hm
  split_ifs at hm with hmx
  · subst hmx
    rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hy
    rw [hy]
    exact h
  · exact absurd rfl hm
end Formalism.MainNotions.FormalGroupSystem.Pf.Gen
