-- Prove2me | solution 1 for FairSelling.GeneralTPS.Good_emptyStage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:42:46.18375+00:00
-- url     : https://prove2.me/submissions/5cb5fe02-9d1d-45e1-b62d-ccc978bb4f7b

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefx
import Definitions.Def_RequestProject_TPSSefxGeneral
import Theorems.Thm_FairSelling_GeneralTPS_pool_emptyStage
import Theorems.Thm_FairSelling_GeneralTPS_truncBundle_univ
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.GeneralTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling.GeneralTPS
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) (hn : 0 < n)
    (hp : ∀ g, 0 ≤ p g) : (emptyStage G n).Good v p eps := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hden : (2 * (n:ℝ) - 1) ≠ 0 := by intro h; linarith
  refine ⟨fun i _ => ⟨rfl, rfl⟩, fun i j _ => by simp [emptyStage],
    fun i => by simp [emptyStage], fun i => le_rfl, le_rfl, by simp [emptyStage], ?_, ?_, ?_⟩
  · intro i hi; exact absurd hi (by simp [emptyStage])
  · intro i hi; exact absurd hi (by simp [emptyStage])
  · intro j _
    rw [pool_emptyStage, truncBundle_univ (v j) p hn hp]
    show (2 * ((n : ℝ) - ((∅ : Finset (Fin n)).card : ℝ)) - 1) * thr v p j
      ≤ (n : ℝ) * TPS n (v j) p + (emptyStage G n).bank
    simp only [Finset.card_empty, Nat.cast_zero, sub_zero, emptyStage, add_zero]
    unfold thr
    rw [show (2 * (n : ℝ) - 1) * (((n : ℝ) / (2 * n - 1)) * TPS n (v j) p)
        = (n : ℝ) * TPS n (v j) p by field_simp]
end FairSelling.GeneralTPS
