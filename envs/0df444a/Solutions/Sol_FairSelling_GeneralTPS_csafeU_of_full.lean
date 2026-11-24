-- Prove2me | solution 1 for FairSelling.GeneralTPS.csafeU_of_full
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:39:20.94773+00:00
-- url     : https://prove2.me/submissions/b4ddd6bb-5b33-4aa6-b9e4-22ee0b35cbb2

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefx
import Definitions.Def_RequestProject_TPSSefxGeneral
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.GeneralTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling.GeneralTPS
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) {s : Stage G n}
    (hs : s.Good v p eps) (hfull : s.served = Finset.univ) (i j : Fin n) :
    CSafeU v p eps s.bundle s.cash i j := by
  have hj : j ∈ s.served := by rw [hfull]; exact Finset.mem_univ j
  have hi : i ∈ s.served := by rw [hfull]; exact Finset.mem_univ i
  have hg : s.guar v p i = vbarSum (v i) p (s.bundle i) + s.cash i := by
    simp [Stage.guar, hi]
  have hsafe := hs.2.2.2.2.2.2.2.1 j hj i
  rw [Stage.Safe, hg] at hsafe
  rcases hsafe with h | ⟨h1, h2, h3⟩
  · exact Or.inl (by linarith)
  · exact Or.inr ⟨h1, h2, fun g hgm => by have := h3 g hgm; linarith⟩
end FairSelling.GeneralTPS
