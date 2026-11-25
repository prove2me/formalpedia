-- Prove2me | solution 1 for Formalism.L2.Pj.LocAlg.yv_succAbove
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:39:00.407168+00:00
-- url     : https://prove2.me/submissions/cc9ced01-7b01-446f-86e2-5cfada67af63

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalIntegralPolynomials_LocStructSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalIntegralPolynomials_ExistsValuationAdaptedIndex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.LocAlg
open ReciprocityTheory.ChartRestriction.G.T0 MvPolynomial
variable {Ω : Type} [Field Ω] {D N : ℕ}
namespace Formalism.L2.Pj.LocAlg
theorem _root_.solution (jc : Fin (N + 1)) (x : Fin N → Ω) (k : Fin N) : yv jc x (jc.succAbove k) = x k := by
  unfold yv
  exact Fin.insertNth_apply_succAbove (α := fun _ => Ω) jc 1 x k
end Formalism.L2.Pj.LocAlg
