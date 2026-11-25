-- Prove2me | solution 1 for Erdos679.eventually_shifted_log_primeProduct_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:42:13.122476+00:00
-- url     : https://prove2.me/submissions/cdccbbd1-952d-439b-9e01-3cd914838f67

module
public import Definitions.Def_Erdos679_Analytic
public import Definitions.Def_Erdos679_Gap
public import Definitions.Def_Erdos679_CRT
public import Definitions.Def_Erdos679AdditiveRefutation_Solution
public import Theorems.Thm_Erdos679_eventually_log_primeProduct_gt
public import Theorems.Thm_Erdos679_primeProduct_pos


set_option autoImplicit false
@[expose] public section
public section
open Filter Real
open scoped Topology
open Erdos679
namespace Erdos679
theorem _root_.solution (K : ℕ) :
    ∀ᶠ m : ℕ in atTop, m * (log m - 2) < log ((primeProduct m + K : ℕ) : ℝ) := by
  filter_upwards [eventually_log_primeProduct_gt] with m hm
  apply hm.trans_le
  apply Real.log_le_log (Nat.cast_pos.mpr (primeProduct_pos m))
  exact_mod_cast (Nat.le_add_right (primeProduct m) K)
end Erdos679
