-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.dualWeylModuleMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:44.98122+00:00
-- url     : https://prove2.me/submissions/3bc49753-5f4e-42c1-8620-f6b0a4251a01

import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LSatLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_lsat_isWH_map
import Theorems.Thm_Formalism_GradedWeylDivisibility_lsat_map_colAddGen
import Theorems.Thm_Formalism_GradedWeylDivisibility_lsat_mem_dualWeyl


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution : DualWeylMap := by
  intro R S _ _ φ r n ν f hf
  rw [lsat_mem_dualWeyl] at hf ⊢
  refine ⟨lsat_isWH_map φ _ _ f hf.1, fun l j hlj => ?_⟩
  rw [← lsat_map_colAddGen, hf.2 l j hlj, map_rename]
end Formalism.GradedWeylDivisibility
