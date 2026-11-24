-- Prove2me | solution 1 for FairChores.exists_reducedC
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:02:31.541797+00:00
-- url     : https://prove2.me/submissions/864da032-539a-493e-b6d5-a9ed4b51c911

import Mathlib
import Definitions.Def_RequestProject_ChoresMMSPartition
import Definitions.Def_RequestProject_ChoresPreAlloc
import Definitions.Def_RequestProject_ChoresTwoAgents
import Theorems.Thm_FairChores_reduce_to_oneC
import Theorems.Thm_FairChores_cbarSum_empty
import Theorems.Thm_FairChores_cbarSum_le_sum
import Theorems.Thm_FairChores_exists_MMS_partition_chores
import Theorems.Thm_FairChores_exists_shrink
attribute [local simp] FairChores.cbarSum_empty



set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
namespace FairChores
theorem _root_.solution (c p : T → ℝ) (hc : ∀ t, 0 ≤ c t) (hp : ∀ t, 0 ≤ p t) :
    ∃ (A : Fin 2 → Finset T) (s : Finset T) (q : Fin 2 → ℝ),
      ConfigC c p (MMS 2 c p) A s q ∧ s.card ≤ 1 := by
  classical
  obtain ⟨o, hovalid, hle⟩ := exists_MMS_partition_chores (n := 2) (by norm_num) c p hc hp
  obtain ⟨hdo, hdk, hcov, hpay0, hbudget⟩ := hovalid
  obtain ⟨q, hq0, hqle, hqsum⟩ :=
    exists_shrink (n := 2) (bill := ∑ t ∈ o.outsourced, p t)
      (Finset.sum_nonneg fun t _ => hp t) o.pay hpay0 hbudget
  have hcfg : ConfigC c p (MMS 2 c p) o.kept o.outsourced q := by
    refine ⟨fun i j hij => hdk i j hij, fun i => hdo i, hcov, hq0, hqsum, fun i => ?_⟩
    have h1 : cbarSum c p (o.kept i) ≤ ∑ t ∈ o.kept i, c t := cbarSum_le_sum c p _
    have h2 := hle i
    simp only [cost] at h2
    linarith [hqle i]
  exact reduce_to_oneC c p hp (MMS 2 c p) o.outsourced.card o.kept o.outsourced q hcfg le_rfl
end FairChores
