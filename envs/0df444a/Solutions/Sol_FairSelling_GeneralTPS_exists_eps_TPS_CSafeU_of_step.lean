-- Prove2me | solution 1 for FairSelling.GeneralTPS.exists_eps_TPS_CSafeU_of_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:45:06.087042+00:00
-- url     : https://prove2.me/submissions/1b8343f7-979e-4721-961d-4428f664a420

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefx
import Definitions.Def_RequestProject_TPSSefxGeneral
import Theorems.Thm_FairSelling_GeneralTPS_Good_emptyStage
import Theorems.Thm_FairSelling_GeneralTPS_csafeU_of_full
import Theorems.Thm_FairSelling_GeneralTPS_descent
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.GeneralTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling.GeneralTPS
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hp : ∀ g, 0 ≤ p g) (eps : ℝ) (heps : 0 < eps)
    (hstep : ImprovementStep v p eps) :
    ∃ (A : Fin n → Finset G) (F : Finset G) (q : Fin n → ℝ),
      (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧ (∀ i, Disjoint F (A i)) ∧
      (∀ i, 0 ≤ q i) ∧ (∑ i, q i ≤ ∑ g ∈ F, p g) ∧
      (∀ i, ((n : ℝ) / (2 * n - 1)) * TPS n (v i) p ≤ vbarSum (v i) p (A i) + q i) ∧
      (∀ i j, CSafeU v p eps A q i j) := by
  obtain ⟨s, hs, hfull⟩ :=
    descent v p eps hp heps hstep n (emptyStage G n) (Good_emptyStage v p eps hn hp)
      (by simp [emptyStage])
  refine ⟨s.bundle, s.soldSet, s.cash, hs.2.1, hs.2.2.1, hs.2.2.2.1, ?_, ?_, ?_⟩
  · have := hs.2.2.2.2.2.1
    have hb := hs.2.2.2.2.1
    linarith
  · intro i
    exact hs.2.2.2.2.2.2.1 i (by rw [hfull]; exact Finset.mem_univ i)
  · exact csafeU_of_full v p eps hs hfull
end FairSelling.GeneralTPS
