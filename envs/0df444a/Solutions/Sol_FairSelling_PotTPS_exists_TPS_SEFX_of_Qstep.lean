-- Prove2me | solution 1 for FairSelling.PotTPS.exists_TPS_SEFX_of_Qstep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:01:05.54464+00:00
-- url     : https://prove2.me/submissions/77bc851e-89de-4504-a38c-3f5dedc6a267

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPot
import Theorems.Thm_FairSelling_PotTPS_QStage_toStage_served
import Theorems.Thm_FairSelling_PotTPS_QStage_toStage_bundle
import Theorems.Thm_FairSelling_PotTPS_QStage_toStage_cash
import Theorems.Thm_FairSelling_PotTPS_QStage_toStage_soldSet
import Theorems.Thm_FairSelling_PotTPS_QStage_good_toStage
import Theorems.Thm_FairSelling_PotTPS_good_emptyQStage
import Theorems.Thm_FairSelling_PotTPS_qdescent
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_bundle
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_cash
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_served
import Theorems.Thm_FairSelling_ChargeTPS_good_toStage
import Theorems.Thm_FairSelling_GeneralTPS_csafeU_of_full
import Theorems.Thm_FairSelling_GeneralTPS_epsSEFXu_unifiedOutcome
import Theorems.Thm_FairSelling_TPS_nonneg
import Theorems.Thm_FairSelling_lemma11_TPS_u
import Theorems.Thm_FairSelling_restrictVal_mem
import Theorems.Thm_FairSelling_unifiedOutcome_valid
import Theorems.Thm_FairSelling_util_unifiedOutcome
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_bundle
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_cash
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_served
attribute [local simp] FairSelling.restrictVal_mem


attribute [local simp] FairSelling.PotTPS.QStage.toStage_served
attribute [local simp] FairSelling.PotTPS.QStage.toStage_bundle
attribute [local simp] FairSelling.PotTPS.QStage.toStage_cash
attribute [local simp] FairSelling.PotTPS.QStage.toStage_soldSet

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PotTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling.PotTPS
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hp : ∀ g, 0 ≤ p g) (hstep : ∀ eps : ℝ, 0 < eps → QImprovementStep v p eps) :
    ∃ o : Outcome G n, o.Valid p ∧
      (∀ i, ((n : ℝ) / (2 * n - 1)) * TPS n (v i) p ≤ util (v i) o i) ∧ SEFX v p o := by
  classical
  refine lemma11_TPS_u v p ((n : ℝ) / (2 * n - 1)) ?_
  intro eps heps
  obtain ⟨s0, hs0, hs0full⟩ := qdescent v p eps hn hp heps (hstep eps heps) n
    (emptyQStage G n) (good_emptyQStage v p eps) (by simp [emptyQStage])
  set s := s0.toStage with hsdef
  have hs : s.Good v p eps := QStage.good_toStage hn hp heps.le hs0
  have hfulls : s.served = Finset.univ := hs0full
  obtain ⟨A, F, q, hAdisj, hFdisj, hq0, hqsum, hserve, hsafe⟩ :
      ∃ (A : Fin n → Finset G) (F : Finset G) (q : Fin n → ℝ),
        (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧ (∀ i, Disjoint F (A i)) ∧
        (∀ i, 0 ≤ q i) ∧ (∑ i, q i ≤ ∑ g ∈ F, p g) ∧
        (∀ i, ((n : ℝ) / (2 * n - 1)) * TPS n (v i) p ≤ vbarSum (v i) p (A i) + q i) ∧
        (∀ i j, GeneralTPS.CSafeU v p eps A q i j) := by
    refine ⟨s.bundle, s.soldSet, s.cash, hs.2.1, hs.2.2.1, hs.2.2.2.1, ?_, ?_, ?_⟩
    · have := hs.2.2.2.2.2.1
      have hb := hs.2.2.2.2.1
      linarith
    · intro i
      exact hs.2.2.2.2.2.2.1 i (by rw [hfulls]; exact Finset.mem_univ i)
    · exact GeneralTPS.csafeU_of_full v p eps hs hfulls
  refine ⟨unifiedOutcome v p A F q, unifiedOutcome_valid v p hp A F q hAdisj hFdisj hq0 hqsum,
    ?_, GeneralTPS.epsSEFXu_unifiedOutcome v p eps A F q hsafe⟩
  intro i
  rw [util_unifiedOutcome]
  have hTPS : (0:ℝ) ≤ TPS n (v i) p := TPS_nonneg (n := n) (v i) p hp
  nlinarith [hserve i]
end FairSelling.PotTPS
