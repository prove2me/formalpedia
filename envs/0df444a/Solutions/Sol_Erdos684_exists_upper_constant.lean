-- Prove2me | solution 1 for Erdos684.exists_upper_constant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:29:54.551728+00:00
-- url     : https://prove2.me/submissions/b90836b1-1671-4408-96a0-77f540178482

module
public import Definitions.Def_Erdos684_Lower
public import Definitions.Def_Erdos684_Averaging
public import Definitions.Def_Erdos684_Analytic
public import Definitions.Def_Erdos684ElementaryBounds_Solution
public import Theorems.Thm_Erdos684_upper_bound

set_option autoImplicit false
@[expose] public section
public section
open Filter Real Finset
open scoped Topology
open Erdos684
namespace Erdos684
theorem _root_.solution :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∃ k ≤ n,
      (k : ℝ) ≤ C * (log (n : ℝ)) ^ 2 ∧ n ^ 2 < smallPrimePart n k := by
  exact ⟨514, by norm_num, upper_bound⟩
end Erdos684
