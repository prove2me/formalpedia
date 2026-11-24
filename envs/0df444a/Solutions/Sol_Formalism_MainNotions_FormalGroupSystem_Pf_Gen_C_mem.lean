-- Prove2me | solution 1 for Formalism.MainNotions.FormalGroupSystem.Pf.Gen.C_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:39:04.383793+00:00
-- url     : https://prove2.me/submissions/bbf4f3c4-6d80-4c28-a393-34c194bd999e

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
theorem _root_.solution {π : σ → Pl} {v : Pl} (c : R) : (MvPowerSeries.C c : MvPowerSeries σ R) ∈ SuppOn π v := by
  classical
  intro m hm y hy
  rw [MvPowerSeries.coeff_C] at hm
  split_ifs at hm with h0
  · subst h0
    simp at hy
  · exact absurd rfl hm
end Formalism.MainNotions.FormalGroupSystem.Pf.Gen
