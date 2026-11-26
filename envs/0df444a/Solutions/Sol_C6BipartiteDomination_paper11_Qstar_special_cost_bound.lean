-- Prove2me | solution 1 for C6BipartiteDomination.paper11_Qstar_special_cost_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:05:43.346459+00:00
-- url     : https://prove2.me/submissions/20925f14-6a93-4123-b10b-c8481a7b0adb

import Definitions.Def_C6BipartiteDomination_PaperSection10
import Definitions.Def_C6BipartiteDomination_PaperSection11
import Theorems.Thm_C6BipartiteDomination_paper10_lemma_10_1


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
    7 * ((paper10SpecialQSet G hCan hmax).card : ℤ) ≤
      7 * ((incidenceTotal G D - (Z0Part G D).card : ℕ) : ℤ) := by
  have h10 := paper10_lemma_10_1 G hCan hmax hNoIso
  have hcast : ((paper10SpecialQSet G hCan hmax).card : ℤ) ≤
      ((incidenceTotal G D - (Z0Part G D).card : ℕ) : ℤ) := by
    exact_mod_cast h10
  nlinarith
end C6BipartiteDomination
