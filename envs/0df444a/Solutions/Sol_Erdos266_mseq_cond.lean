-- Prove2me | solution 1 for Erdos266.mseq_cond
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:49:08.239476+00:00
-- url     : https://prove2.me/submissions/4819302f-9a8a-40df-9e0e-6f434a57c5b9

module
public import Definitions.Def_Erdos266_LatticeLemma
public import Definitions.Def_Erdos266_Growth
public import Definitions.Def_Erdos266_Algorithm
public import Theorems.Thm_Erdos266_growth_eventually


set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution (d : ℕ) : ∀ k, mseq (d + 1) ≤ k → ∀ i : ℕ, i < d + 1 →
    DL (d + 1) * (1 / (bigN k : ℝ) ^ (i + 2) + (bigM k : ℝ) ^ 2 / (bigN k : ℝ) ^ (i + 3))
      ≤ εA (d + 2) * (bigM (k + 1) : ℝ) / (bigN (k + 1) : ℝ) ^ (i + 2) := by
  intro k hk i hi
  have hspec := (growth_eventually (d + 1) (DL (d + 1)) (εA (d + 2)) (DL_pos (d + 1))
    (εA_pos (d + 2))).choose_spec
  refine hspec.2 k ?_ i hi
  exact le_trans (le_max_right _ _) hk
end Erdos266
