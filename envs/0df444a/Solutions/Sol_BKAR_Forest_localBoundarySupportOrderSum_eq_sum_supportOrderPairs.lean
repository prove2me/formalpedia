-- Prove2me | solution 1 for BKAR.Forest.localBoundarySupportOrderSum_eq_sum_supportOrderPairs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:49:27.291388+00:00
-- url     : https://prove2.me/submissions/6647850c-9847-4a30-a62b-a84b74d27299

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
import Theorems.Thm_BKAR_Forest_localBoundarySupportOrderSum_def


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    localBoundarySupportOrderSum choices F pref prefixTs top ρ =
      Finset.sum (supportOrderPairs V)
        (fun x =>
          localBoundarySupportOrderContribution choices F pref prefixTs top
            x.1 x.2 ρ) := by
  rw [localBoundarySupportOrderSum_def, supportOrderPairs, Finset.sum_sigma]
end BKAR.Forest
