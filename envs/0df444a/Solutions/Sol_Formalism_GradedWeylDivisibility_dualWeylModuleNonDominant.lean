-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.dualWeylModuleNonDominant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:20.549324+00:00
-- url     : https://prove2.me/submissions/f3fd3183-59d4-428b-b1fc-45a10a1c19ca

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LNondomLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylNonDom
import Theorems.Thm_Formalism_GradedWeylDivisibility_nd_main

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
variable {R : Type*} [CommRing R] {r n : ℕ}
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution : DualWeylNonDom := by
  intro R _ _ _ r n ν ⟨l, j, hlj, hν⟩
  rw [Submodule.eq_bot_iff]
  intro f hf
  rw [dualWeyl, Submodule.mem_inf, mem_weightedHomogeneousSubmodule] at hf
  obtain ⟨hhom, hinv⟩ := hf
  have h1 := Submodule.mem_iInf _ |>.1 hinv l
  have h2 := Submodule.mem_iInf _ |>.1 h1 j
  have h3 := Submodule.mem_iInf _ |>.1 h2 hlj
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, AlgHom.toLinearMap_apply,
    AlgHom.toLinearMap_apply] at h3
  exact nd_main ν hlj hν f hhom h3
end Formalism.GradedWeylDivisibility
