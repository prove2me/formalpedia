-- Prove2me | solution 1 for DeletionCode.PaperParameters.le_two_pow_of_L_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:49:33.09533+00:00
-- url     : https://prove2.me/submissions/be676f28-e8ab-4abd-8b98-0f8cb72d1400

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
theorem _root_.solution (n R : ℕ) (hR : L n < R) : n ≤ 2 ^ R := by
  have hc : Nat.clog 2 n ≤ R := by rw [L_eq] at hR; omega
  exact (Nat.le_pow_clog (by decide : 1 < 2) n).trans
    (Nat.pow_le_pow_right (by decide : 0 < 2) hc)
end DeletionCode.PaperParameters
