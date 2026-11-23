-- Prove2me | solution 1 for Formalism.REAL.factorAction_apply_general
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:11:05.030456+00:00
-- url     : https://prove2.me/submissions/1ec7864c-96d0-432a-a8c0-a8d9e786e610

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
theorem _root_.solution {j : ℕ} (i : Fin j) (c d : Fin n) (F : Arr V n j) (α : Fin j → Fin n × Fin n) :
    factorAction i c d F α = (if (α i).1 = c then F (Function.update α i (d, (α i).2)) else 0) -
      (if (α i).2 = d then F (Function.update α i ((α i).1, c)) else 0) := by
  simp only [factorAction, arrTo, arrOf, LinearMap.comp_apply, LinearEquiv.coe_coe]
  by_cases h1 : (α i).1 = c <;> by_cases h2 : (α i).2 = d <;> simp [h1, h2]
end Formalism.REAL
