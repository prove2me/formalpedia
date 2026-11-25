-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.swap_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:05:19.470621+00:00
-- url     : https://prove2.me/submissions/486dc828-c8ce-4c35-ac69-9138760f7def

import Definitions.Def_Formalism_FlagUnipotentLattices_MemLpTwoOfOneTop
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_InterlacingOfBlocksSecondCase

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S8 MeasureTheory Filter Topology TensorProduct Finset
set_option linter.all false
noncomputable section
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {κ q i : ℕ} (hq : q ≤ κ) (hi : i < κ) : Equiv.swap 0 q (i + 1) < κ + 1 := by
  simp only [Equiv.swap_apply_def]; split_ifs <;> omega
end Formalism.HermitianLatticeCounting.P
