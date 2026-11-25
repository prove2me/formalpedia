-- Prove2me | solution 1 for DedekindSubgroups.sawtooth_div_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:04:22.08554+00:00
-- url     : https://prove2.me/submissions/9f45b1fe-cef7-4504-99e6-6d7d197e0a92

module
public import Definitions.Def_DedekindSubgroups_Basic
public import Definitions.Def_DedekindSubgroups_Meyer

set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups
variable {h h' k : ℕ}
namespace DedekindSubgroups
theorem _root_.solution {r k : ℕ} (hr0 : 0 < r) (hrk : r < k) :
    sawtooth ((r : ℚ) / k) = (r : ℚ) / k - 1 / 2 := by
  have hk : (0 : ℚ) < k := by exact_mod_cast lt_trans hr0 hrk
  have hfr : Int.fract ((r : ℚ) / k) = (r : ℚ) / k := by
    rw [Int.fract_eq_self]
    refine ⟨by positivity, ?_⟩
    rw [div_lt_one hk]; exact_mod_cast hrk
  have hne : (r : ℚ) / k ≠ 0 := by
    have : (0 : ℚ) < r := by exact_mod_cast hr0
    positivity
  simp [sawtooth, hfr, hne]
end DedekindSubgroups
