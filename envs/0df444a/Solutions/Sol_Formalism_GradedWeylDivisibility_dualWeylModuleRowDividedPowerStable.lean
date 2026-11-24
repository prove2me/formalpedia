-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.dualWeylModuleRowDividedPowerStable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:10:14.571055+00:00
-- url     : https://prove2.me/submissions/93944bb0-bfcd-43fe-99c3-4f1a98b12540

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_RowDivStable
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowdiv_mem_dualWeyl_iff
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDiv_homog
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDiv_colAddGen

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
theorem _root_.solution : RowDivStable := by
  intro R _ r n ν a b k f hf
  rw [rowdiv_mem_dualWeyl_iff] at hf ⊢
  exact ⟨rowDiv_homog R ν a b k f hf.1, fun l j hlj => rowDiv_colAddGen R a b k l j f (hf.2 l j hlj)⟩
end Formalism.GradedWeylDivisibility
