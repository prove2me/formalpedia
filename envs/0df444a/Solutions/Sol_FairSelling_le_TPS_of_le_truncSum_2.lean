-- Prove2me | solution 2 for FairSelling.le_TPS_of_le_truncSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:40:36.711796+00:00
-- url     : https://prove2.me/submissions/2a066260-8a82-4b56-bed7-f436ca90da88

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TPSCompute
import Theorems.Thm_FairSelling_TPSset_bddAbove


set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [DecidableEq G]
namespace FairSelling
theorem _root_.solution (v p : G → ℝ) {t : ℝ} (ht : t ≤ truncSum n v p t) :
    t ≤ TPS n v p :=
  le_csSup (TPSset_bddAbove v p) ht
end FairSelling
