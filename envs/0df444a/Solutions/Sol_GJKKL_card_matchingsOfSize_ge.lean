-- Prove2me | solution 1 for GJKKL.card_matchingsOfSize_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:12:24.873364+00:00
-- url     : https://prove2.me/submissions/633d6acd-6d81-4df3-ab1c-6d8985fa701e

module
public import Definitions.Def_GJKKL_Greedy_Process
public import Definitions.Def_GJKKL_History_Freedman
public import Definitions.Def_GJKKL_Greedy_Counting
public import Theorems.Thm_GJKKL_prob_mul_prod_le_card

set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset History
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace GJKKL
theorem _root_.solution (H : Finset (Finset V)) (hne : ∀ e ∈ H, e.Nonempty)
    (g : ℕ → ℝ) (hg : ∀ i, 0 ≤ g i) (m : ℕ) :
    prob (greedyKernel H) m (ManyAvail H g) * (∏ i ∈ range m, g i) / m.factorial ≤
      (matchingsOfSize H m).card := by
  rw [div_le_iff₀ (by positivity), mul_comm _ (m.factorial : ℝ)]
  exact prob_mul_prod_le_card H hne g hg m
end GJKKL
