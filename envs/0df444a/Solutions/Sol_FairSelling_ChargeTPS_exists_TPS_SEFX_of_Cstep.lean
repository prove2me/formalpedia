-- Prove2me | solution 1 for FairSelling.ChargeTPS.exists_TPS_SEFX_of_Cstep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:47:33.181076+00:00
-- url     : https://prove2.me/submissions/474559c2-a641-4b22-b195-67931dd6896b

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefxGeneral
import Definitions.Def_RequestProject_TPSSefxCharge
import Theorems.Thm_FairSelling_ChargeTPS_exists_eps_TPS_CSafeU_of_Cstep
import Theorems.Thm_FairSelling_GeneralTPS_epsSEFXu_unifiedOutcome
import Theorems.Thm_FairSelling_TPS_nonneg
import Theorems.Thm_FairSelling_lemma11_TPS_u
import Theorems.Thm_FairSelling_unifiedOutcome_valid
import Theorems.Thm_FairSelling_util_unifiedOutcome


set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling.ChargeTPS
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hp : ∀ g, 0 ≤ p g) (hstep : ∀ eps : ℝ, 0 < eps → CImprovementStep v p eps) :
    ∃ o : Outcome G n, o.Valid p ∧
      (∀ i, ((n : ℝ) / (2 * n - 1)) * TPS n (v i) p ≤ util (v i) o i) ∧ SEFX v p o := by
  classical
  refine lemma11_TPS_u v p ((n : ℝ) / (2 * n - 1)) ?_
  intro eps heps
  obtain ⟨A, F, q, hAdisj, hFdisj, hq0, hqsum, hserve, hsafe⟩ :=
    exists_eps_TPS_CSafeU_of_Cstep v p hn hp eps heps (hstep eps heps)
  refine ⟨unifiedOutcome v p A F q, unifiedOutcome_valid v p hp A F q hAdisj hFdisj hq0 hqsum,
    ?_, GeneralTPS.epsSEFXu_unifiedOutcome v p eps A F q hsafe⟩
  intro i
  rw [util_unifiedOutcome]
  have hTPS : (0:ℝ) ≤ TPS n (v i) p := TPS_nonneg (n := n) (v i) p hp
  nlinarith [hserve i]
end FairSelling.ChargeTPS
