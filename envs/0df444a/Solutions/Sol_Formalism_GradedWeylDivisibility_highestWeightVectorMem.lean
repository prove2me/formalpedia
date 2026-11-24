-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.highestWeightVectorMem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:23.688395+00:00
-- url     : https://prove2.me/submissions/87eae7e8-3a72-475f-aec9-82d4ad498459

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_SumIcoTsubTelescope
import Theorems.Thm_Formalism_GradedWeylDivisibility_hw_weight_eq
import Theorems.Thm_Formalism_GradedWeylDivisibility_lpMinor_mem
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeyl_of_eq
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeyl_pow
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeyl_prod


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
theorem _root_.solution : HWMem := by
  unfold HWMem
  intro R _ r n hn ν hν
  unfold hw
  refine dualWeyl_of_eq ?_ (hw_weight_eq ν hν)
  exact dualWeyl_prod Finset.univ
    (fun s : Fin n => (ν s - nuNext ν s) • initW n (s.val + 1))
    (fun s : Fin n =>
      lpMinor R (s.val + 1) (by omega) (by omega) ^ (ν s - nuNext ν s))
    (fun s _ => dualWeyl_pow (lpMinor_mem _ _ _) _)
end Formalism.GradedWeylDivisibility
