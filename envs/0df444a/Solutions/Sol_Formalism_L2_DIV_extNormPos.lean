-- Prove2me | solution 1 for Formalism.L2.DIV.extNormPos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:09:05.599137+00:00
-- url     : https://prove2.me/submissions/3682893c-0916-4e3a-b1d8-236cb70b3e34

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
import Theorems.Thm_Formalism_L2_DIV_fockSQ
import Theorems.Thm_Formalism_L2_DIV_map_extremal
import Theorems.Thm_Formalism_GradedWeylDivisibility_fockQPos
import Theorems.Thm_Formalism_GradedWeylDivisibility_hwNe


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.BasicNotions
namespace Formalism.L2.DIV
theorem _root_.solution : ExtNormPos := by
  intro K _ _ _ ι _ n lam
  refine ⟨∏ τ, Formalism.GradedWeylDivisibility.fockQ (extremal ℚ n (lam τ)) (extremal ℚ n (lam τ)), ?_, ?_⟩
  · refine Finset.prod_pos fun τ _ => ?_
    exact (Formalism.GradedWeylDivisibility.fockQPos _ _ (extremal ℚ n (lam τ))).2 (Formalism.GradedWeylDivisibility.hwNe ℚ n n le_rfl _)
  · unfold extNorm
    rw [map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← fockSQ K, map_extremal]
end Formalism.L2.DIV
