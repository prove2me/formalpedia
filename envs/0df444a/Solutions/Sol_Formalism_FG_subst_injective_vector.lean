-- Prove2me | solution 1 for Formalism.FG.subst_injective_vector
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:55:27.113446+00:00
-- url     : https://prove2.me/submissions/731cc5d6-452b-4007-8c48-38248dc4e63b

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Theorems.Thm_Formalism_FG_InjVAux_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
open Formalism Formalism.FG
open MvPowerSeries
namespace Formalism.FG
theorem _root_.solution : Formalism.FG.SubstInjectiveV.{u, v, w} := by
  intro R _ ι _ _ τ _ f a b hf ha hb h
  funext i
  ext d
  have := InjVAux.main f a b hf ha hb h d.degree i d (by omega)
  rwa [map_sub, sub_eq_zero] at this
end Formalism.FG
