-- Prove2me | solution 1 for DeletionCode.PaperParameters.eventually_threshold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:49:57.271078+00:00
-- url     : https://prove2.me/submissions/9c56edd4-21fb-4aee-a80c-ea5ccc357b5f

import Definitions.Def_DeletionCode_UniqueWordParameters
import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Analysis.Asymptotics.Defs
import Definitions.Def_DeletionCode_PaperParameters
import Theorems.Thm_DeletionCode_PaperParameters_threshold

set_option autoImplicit true
open DeletionCode DeletionCode.PaperParameters
open Filter Asymptotics
open scoped Topology
namespace DeletionCode.PaperParameters
theorem _root_.solution (M : ℕ) : ∀ᶠ n : ℕ in atTop, M ≤ L n := by
  filter_upwards [eventually_ge_atTop (2 ^ M + 1)] with n hn
  exact threshold M n hn
end DeletionCode.PaperParameters
