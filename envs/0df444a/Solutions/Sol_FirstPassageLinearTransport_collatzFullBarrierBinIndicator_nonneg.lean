-- Prove2me | solution 1 for FirstPassageLinearTransport.collatzFullBarrierBinIndicator_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:05:11.811341+00:00
-- url     : https://prove2.me/submissions/66d3fafd-1e55-4ccb-864c-2aa20a1779fc

import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {m : ℕ} (B q : ℝ) (v : Fin m → Bool) :
    0 ≤ collatzFullBarrierBinIndicator B q v := by
  classical
  unfold collatzFullBarrierBinIndicator
  split <;> norm_num
end FirstPassageLinearTransport
