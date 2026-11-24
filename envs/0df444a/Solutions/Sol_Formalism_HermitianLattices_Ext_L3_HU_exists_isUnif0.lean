-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.exists_isUnif0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:09.136779+00:00
-- url     : https://prove2.me/submissions/a9c9da13-f3d0-4dd7-9a8d-2a25386ee774

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SpanPowMulLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NeZeroOfNotMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_exists_unif0


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
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : ∃ π₀ s₀, IsUnif0 𝔭 π₀ s₀ := by
  obtain ⟨π₀, h1, h2, s₀, h3, h4⟩ := exists_unif0 h𝔭
  exact ⟨π₀, s₀, ⟨h1, h2, h3, h4⟩⟩
end Formalism.HermitianLattices.Ext.L3.HU
