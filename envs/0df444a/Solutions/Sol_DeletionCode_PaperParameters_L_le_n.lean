-- Prove2me | solution 1 for DeletionCode.PaperParameters.L_le_n
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:59.553653+00:00
-- url     : https://prove2.me/submissions/155ba3f2-eef3-4c75-816d-f84a06771dfc

import Definitions.Def_DeletionCode_UniqueWordParameters
import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Analysis.Asymptotics.Defs
import Definitions.Def_DeletionCode_PaperParameters
import Theorems.Thm_DeletionCode_PaperParameters_L_eq
section
namespace DeletionCode.PaperParameters
open Filter Asymptotics
open scoped Topology
private theorem affine_le_pow (q : ℕ) : 6 * (q + 6) + 15 ≤ 2 ^ (q + 6) := by
  induction q with
  | zero => norm_num
  | succ q ih =>
    have he : (q + 1) + 6 = (q + 6) + 1 := by omega
    change 6 * ((q + 1) + 6) + 15 ≤ 2 ^ ((q + 1) + 6)
    rw [he, pow_succ]
    omega
end DeletionCode.PaperParameters
end

set_option autoImplicit true
open DeletionCode DeletionCode.PaperParameters
open Filter Asymptotics
open scoped Topology
namespace DeletionCode.PaperParameters
theorem _root_.solution (n : ℕ) (hn : 65 ≤ n) : L n ≤ n := by
  let c := Nat.clog 2 n
  have hc : 6 < c := by
    apply (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mpr
    norm_num
    omega
  have hpow := affine_le_pow (c - 7)
  have he : (c - 7) + 6 = c - 1 := by omega
  rw [he] at hpow
  have hnpow : 2 ^ (c - 1) < n := Nat.pow_lt_of_lt_clog (by omega : c - 1 < c)
  rw [L_eq]
  change 6 * c + 9 ≤ n
  omega
end DeletionCode.PaperParameters
