-- Prove2me | solution 1 for FairSelling.ChargeTPS.exists_eps_TPS_CSafeU_of_Cstep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:46:04.030115+00:00
-- url     : https://prove2.me/submissions/43b996ae-006c-48c2-919b-5cb3d4bf4744

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefxGeneral
import Definitions.Def_RequestProject_TPSSefxCharge
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_served
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_bundle
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_cash
import Theorems.Thm_FairSelling_ChargeTPS_good_toStage
import Theorems.Thm_FairSelling_ChargeTPS_good_emptyCStage
import Theorems.Thm_FairSelling_ChargeTPS_cdescent
import Theorems.Thm_FairSelling_GeneralTPS_csafeU_of_full
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.restrictVal_mem


attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_served
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_bundle
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_cash

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling.ChargeTPS
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hp : ∀ g, 0 ≤ p g) (eps : ℝ) (heps : 0 < eps) (hstep : CImprovementStep v p eps) :
    ∃ (A : Fin n → Finset G) (F : Finset G) (q : Fin n → ℝ),
      (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧ (∀ i, Disjoint F (A i)) ∧
      (∀ i, 0 ≤ q i) ∧ (∑ i, q i ≤ ∑ g ∈ F, p g) ∧
      (∀ i, ((n : ℝ) / (2 * n - 1)) * TPS n (v i) p ≤ vbarSum (v i) p (A i) + q i) ∧
      (∀ i j, GeneralTPS.CSafeU v p eps A q i j) := by
  classical
  obtain ⟨s0, hs0, hfull⟩ := cdescent v p eps hn hp heps hstep n
    (emptyCStage G n) (good_emptyCStage v p eps) (by simp [emptyCStage])
  set s := s0.toStage with hsdef
  have hs : s.Good v p eps := good_toStage v p eps hn heps.le hp hs0
  have hfulls : s.served = Finset.univ := hfull
  refine ⟨s.bundle, s.soldSet, s.cash, hs.2.1, hs.2.2.1, hs.2.2.2.1, ?_, ?_, ?_⟩
  · have := hs.2.2.2.2.2.1
    have hb := hs.2.2.2.2.1
    linarith
  · intro i
    exact hs.2.2.2.2.2.2.1 i (by rw [hfulls]; exact Finset.mem_univ i)
  · exact GeneralTPS.csafeU_of_full v p eps hs hfulls
end FairSelling.ChargeTPS
