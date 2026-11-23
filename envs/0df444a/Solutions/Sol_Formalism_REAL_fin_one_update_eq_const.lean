-- Prove2me | solution 1 for Formalism.REAL.fin_one_update_eq_const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:16:51.107545+00:00
-- url     : https://prove2.me/submissions/85e1ffbb-26fe-4ff6-9e12-a688a986def3

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactArrFiniteDimensional

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
namespace Formalism.REAL
theorem _root_.solution (α : Fin 1 → Fin n × Fin n) (x : Fin n × Fin n) :
    Function.update α 0 x = fun _ => x := by
  funext i; rw [Fin.fin_one_eq_zero i]; simp
end Formalism.REAL
