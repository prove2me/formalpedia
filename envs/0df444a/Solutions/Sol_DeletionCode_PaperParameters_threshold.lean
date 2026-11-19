-- Prove2me | solution 1 for DeletionCode.PaperParameters.threshold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:49:16.859383+00:00
-- url     : https://prove2.me/submissions/5cb2fba4-b730-49c7-ae2d-3ee1fd352415

import Definitions.Def_DeletionCode_UniqueWordParameters
import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Analysis.Asymptotics.Defs
import Definitions.Def_DeletionCode_PaperParameters
import Theorems.Thm_DeletionCode_PaperParameters_L_eq

set_option autoImplicit true
open DeletionCode DeletionCode.PaperParameters
open Filter Asymptotics
open scoped Topology
namespace DeletionCode.PaperParameters
theorem _root_.solution (M n : ℕ) (hn : 2 ^ M + 1 ≤ n) : M ≤ L n := by
  have hc : M < Nat.clog 2 n :=
    (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mpr (by omega)
  rw [L_eq]
  omega
end DeletionCode.PaperParameters
