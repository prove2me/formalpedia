-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.ldiag_prod_univ_eq_range
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:20.491143+00:00
-- url     : https://prove2.me/submissions/f0d2c544-9fcb-461f-bb98-e706adb21bdf

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DomPow
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldiag_ext_fin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {r : ℕ} (t : Fin r → ℝ) (μ : Fin r → ℕ) :
    ∏ a : Fin r, t a ^ μ a = ∏ a ∈ range r, ldiagExt t a ^ ldiagExt μ a := by
  rw [← Fin.prod_univ_eq_prod_range (fun i : ℕ => ldiagExt t i ^ ldiagExt μ i) r]
  refine Finset.prod_congr rfl fun a _ => ?_
  simp only [ldiag_ext_fin]
end Formalism.GradedWeylDivisibility
