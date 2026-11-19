-- Prove2me | solution 1 for DeletionCode.PaperParameters.L_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:30:20.46935+00:00
-- url     : https://prove2.me/submissions/cf41219d-d4d3-4d5e-8305-90690424fb7f

import Definitions.Def_DeletionCode_UniqueWordParameters
import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Analysis.Asymptotics.Defs
import Definitions.Def_DeletionCode_PaperParameters

set_option autoImplicit true
open DeletionCode DeletionCode.PaperParameters
open Filter Asymptotics
open scoped Topology
namespace DeletionCode.PaperParameters
theorem _root_.solution (n : ℕ) : L n = 6 * Nat.clog 2 n + 9 := by
  unfold L k HeaderRecovery.windowLength UniqueWordParameters.uniquenessLength
  omega
end DeletionCode.PaperParameters
