-- Prove2me | solution 1 for FairSelling.paired_loss_bagfill_reduction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:36:36.043003+00:00
-- url     : https://prove2.me/submissions/55950b94-65a2-438c-8666-6fead69f4dd5

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
import Definitions.Def_RequestProject_MMSPartition
import Definitions.Def_RequestProject_ThreeAgents
import Theorems.Thm_FairSelling_restricted_MMS2_ge
import Theorems.Thm_FairSelling_vbarSum_sdiff


set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (R C : Finset G) (hC : C ⊆ R)
    (hClo : (3/4) * MMS 3 w p ≤ vbarSum w p C)
    (hChi : vbarSum w p C ≤ MMS 3 w p)
    (hR : MMS 3 w p + (3/4) * MMS 3 w p ≤ vbarSum w p R) :
    (3/4) * MMS 3 w p ≤ MMS 2 (restrictVal R w) (restrictVal R p) := by
  apply FairSelling.restricted_MMS2_ge;
  bv_omega;
  exact hp;
  convert Finset.disjoint_sdiff;
  exact inferInstance;
  exact C;
  exact R;
  · assumption;
  · grind;
  · exact hClo;
  · linarith [ vbarSum_sdiff w p hC ]
end FairSelling
