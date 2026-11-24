-- Prove2me | solution 1 for FairSelling.GeneralTPS.exists_TPS_SEFX_of_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:42:51.602942+00:00
-- url     : https://prove2.me/submissions/a3fd757a-2e3d-4310-a98e-5c3e355b9acd

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefx
import Definitions.Def_RequestProject_TPSSefxGeneral
import Theorems.Thm_FairSelling_GeneralTPS_epsSEFXu_unifiedOutcome
import Theorems.Thm_FairSelling_GeneralTPS_exists_eps_TPS_CSafeU_of_step
import Theorems.Thm_FairSelling_TPS_nonneg
import Theorems.Thm_FairSelling_lemma11_TPS_u
import Theorems.Thm_FairSelling_unifiedOutcome_valid
import Theorems.Thm_FairSelling_util_unifiedOutcome


set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.GeneralTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling.GeneralTPS
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hp : ∀ g, 0 ≤ p g)
    (hstep : ∀ eps : ℝ, 0 < eps → ImprovementStep v p eps) :
    ∃ o : Outcome G n, o.Valid p ∧
      (∀ i, ((n : ℝ) / (2 * n - 1)) * TPS n (v i) p ≤ util (v i) o i) ∧ SEFX v p o := by
  classical
  refine lemma11_TPS_u v p ((n : ℝ) / (2 * n - 1)) ?_
  intro eps heps
  obtain ⟨A, F, q, hAdisj, hFdisj, hq0, hqsum, hserve, hsafe⟩ :=
    exists_eps_TPS_CSafeU_of_step v p hn hp eps heps (hstep eps heps)
  refine ⟨unifiedOutcome v p A F q, unifiedOutcome_valid v p hp A F q hAdisj hFdisj hq0 hqsum,
    ?_, epsSEFXu_unifiedOutcome v p eps A F q hsafe⟩
  intro i
  rw [util_unifiedOutcome]
  have hTPS : (0:ℝ) ≤ TPS n (v i) p := TPS_nonneg (n := n) (v i) p hp
  nlinarith [hserve i]
end FairSelling.GeneralTPS
