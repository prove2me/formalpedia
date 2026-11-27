-- Prove2me | solution 1 for C6BipartiteDomination.paper11K3SpecialBudget_cost_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:10:50.484331+00:00
-- url     : https://prove2.me/submissions/67c77772-6ece-42e0-9d09-c250b7a83fc8

import Definitions.Def_C6BipartiteDomination_PaperSection10
import Definitions.Def_C6BipartiteDomination_PaperSection11
import Theorems.Thm_C6BipartiteDomination_paper11K3SpecialBudget_card_le_Qstar
import Theorems.Thm_C6BipartiteDomination_paper11_Qstar_special_cost_bound

set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6)
    (hNoIso : HasNoIsolatedVertices G) :
    7 * ((paper11K3SpecialBudgetVertices G D hCan hmax).card : ℤ) ≤
      7 * ((incidenceTotal G D - (Z0Part G D).card : ℕ) : ℤ) := by
  have hP := paper11K3SpecialBudget_card_le_Qstar G hCan hmax
  have hPc : ((paper11K3SpecialBudgetVertices G D hCan hmax).card : ℤ) ≤
      ((paper10SpecialQSet G hCan hmax).card : ℤ) := by exact_mod_cast hP
  have hQ := paper11_Qstar_special_cost_bound G hCan hmax hNoIso
  nlinarith
end C6BipartiteDomination
