-- Prove2me | solution 1 for Formalism.REAL.theta_map_word_sum_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:46:34.232797+00:00
-- url     : https://prove2.me/submissions/db1b8698-2d7b-4201-b674-dba003c4233d

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
theorem _root_.solution {j : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (F : Arr V n j) :
    thetaA E j F = ∑ α : Fin j → Fin n × Fin n, ew E (List.ofFn α).reverse (F α) := by
  simp [thetaA, arrOf]
end Formalism.REAL
