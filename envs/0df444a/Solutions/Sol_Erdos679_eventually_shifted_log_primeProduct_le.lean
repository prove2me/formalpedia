-- Prove2me | solution 1 for Erdos679.eventually_shifted_log_primeProduct_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:58:41.766144+00:00
-- url     : https://prove2.me/submissions/a777b29e-3365-4704-8311-83920fe32ecf

module
public import Definitions.Def_Erdos679_Analytic
public import Definitions.Def_Erdos679_Gap
public import Definitions.Def_Erdos679_CRT
public import Definitions.Def_Erdos679AdditiveRefutation_Solution
public import Theorems.Thm_Erdos679_log_nat_add_le
public import Theorems.Thm_Erdos679_eventually_log_primeProduct_le
public import Theorems.Thm_Erdos679_primeProduct_pos


set_option autoImplicit false
@[expose] public section
public section
open Filter Real
open scoped Topology
open Erdos679
namespace Erdos679
theorem _root_.solution (K : ℕ) :
    ∀ᶠ m : ℕ in atTop, log ((primeProduct m + K : ℕ) : ℝ) ≤
      m * (log m + log (log m) - (1 / 5 : ℝ)) := by
  have hlim : Tendsto (fun m : ℕ => (K : ℝ) / m) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hsmall := hlim.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 10)
  filter_upwards [eventually_log_primeProduct_le, hsmall,
    eventually_gt_atTop (0 : ℕ)] with m hm hs hm0
  have hmp : (0 : ℝ) < m := Nat.cast_pos.mpr hm0
  have hs' := (div_lt_iff₀ hmp).mp hs
  have hshift := log_nat_add_le (primeProduct m) K (primeProduct_pos m)
  nlinarith
end Erdos679
