-- Prove2me | solution 1 for Formalism.IndefR.LocBrg.pow_anti
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:54:22.153576+00:00
-- url     : https://prove2.me/submissions/b48b5c55-9067-4193-9838-2ed2b9b02345

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LocalNormSurjectivity_FinNormSurj
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LocalNormSurjectivity_WittHS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.LocBrg
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
local notation "vv" => (Valued.v : Valuation L (WithZero (Multiplicative ℤ)))
variable (u : L)
namespace Formalism.IndefR.LocBrg
theorem _root_.solution {γ : WithZero (Multiplicative ℤ)} (hγ : γ ≤ 1) {a b : ℕ} (hab : a ≤ b) : γ ^ b ≤ γ ^ a := by
  first
  | exact pow_le_pow_right_of_le_one' hγ hab
  | exact pow_le_pow_right_of_le_one₀ zero_le' hγ hab
end Formalism.IndefR.LocBrg
