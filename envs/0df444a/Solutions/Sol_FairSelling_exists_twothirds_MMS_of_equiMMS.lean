-- Prove2me | solution 1 for FairSelling.exists_twothirds_MMS_of_equiMMS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:27:35.352068+00:00
-- url     : https://prove2.me/submissions/63909df7-eb23-481a-a870-e5105665c09f

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TwoThirdsCanonical
import Definitions.Def_RequestProject_TwoThirdsLoss
import Definitions.Def_RequestProject_TwoThirdsLemma9
import Definitions.Def_RequestProject_TwoThirds
import Theorems.Thm_FairSelling_servable_stage1
import Theorems.Thm_FairSelling_losses_initial
import Theorems.Thm_FairSelling_restrictVal_mem
import Theorems.Thm_FairSelling_unifiedOutcome_valid
import Theorems.Thm_FairSelling_util_unifiedOutcome
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g)
    (hE : ∀ i, Nonempty (EquiMMS (v i) p (MMS n (v i) p) n)) :
    ∃ o : Outcome G n, o.Valid p ∧ ∀ i, (2 / 3 : ℝ) * MMS n (v i) p ≤ util (v i) o i := by
  classical
  obtain ⟨A, F, q, hAR, hFR, hAdisj, hFdisj, hq0, hqsum, hserve, _⟩ :=
    servable_stage1 v p hn hv hp n Finset.univ Finset.univ 0 (by simp) le_rfl
      (losses_initial v p hE)
  refine ⟨unifiedOutcome v p A F q, ?_, ?_⟩
  · refine unifiedOutcome_valid v p hp A F q hAdisj hFdisj hq0 ?_
    simpa using hqsum
  · intro i
    rw [util_unifiedOutcome]
    exact hserve i (Finset.mem_univ i)
end FairSelling
