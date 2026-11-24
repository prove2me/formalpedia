-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.IsUnif0.ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:00.276586+00:00
-- url     : https://prove2.me/submissions/2f6a6493-1c9d-4f5e-896c-fb8f2fa66252

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SpanPowMulLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NeZeroOfNotMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
open LocalSpans idealPowerSpanBounds localizedQuotients
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K
namespace Formalism.HermitianLattices.Ext.L3.HU
namespace IsUnif0
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} {π₀ s₀ : 𝓞 F} (hu : IsUnif0 𝔭 π₀ s₀) : π₀ ≠ 0 := by
  rintro rfl
  exact hu.notMem (Submodule.zero_mem _)
end IsUnif0
end Formalism.HermitianLattices.Ext.L3.HU
