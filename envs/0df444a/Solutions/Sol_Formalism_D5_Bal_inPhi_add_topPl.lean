-- Prove2me | solution 1 for Formalism.D5.Bal.inPhi_add_topPl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:46:45.654749+00:00
-- url     : https://prove2.me/submissions/e373cd4e-0c6b-4d17-9759-3eaa8472a08e

import Definitions.Def_Formalism_ThickAverageLoss_PartnersToFactorsAt
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset ArithmeticFunction
noncomputable section
namespace Formalism.D5
open Formalism Formalism.CMTypeGaloisData Formalism.WT Formalism.WeightedSieveThreeParameter
namespace Bal
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
private lemma prod_add_fst_fst (x y : E0 × H) : (x + y).1.1 = x.1.1 + y.1.1 := rfl
private lemma topPl_fst_fst_eq_zero (t : H) : (topPl t).1.1 = 0 := rfl
end
end Bal
end Formalism.D5
end
end

set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.D5
open Formalism Formalism.CMTypeGaloisData Formalism.WT Formalism.WeightedSieveThreeParameter
open Formalism.D5.Bal
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Formalism.D5.Bal
theorem _root_.solution (g : E0 × H) (t : H) : InPhi (g + topPl t) ↔ InPhi g := by
  show (g + topPl t).1.1 = 0 ↔ g.1.1 = 0
  rw [prod_add_fst_fst, topPl_fst_fst_eq_zero, add_zero]
end Formalism.D5.Bal
