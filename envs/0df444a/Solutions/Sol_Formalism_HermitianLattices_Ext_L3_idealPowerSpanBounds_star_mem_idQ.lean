-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds.star_mem_idQ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:25:38.823351+00:00
-- url     : https://prove2.me/submissions/fb280e79-d426-462e-a800-b4bbd4a26a26

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardLiftMatrix
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardQuotExtPPow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_star_mk
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_mem_idQ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_conjO_mem_pow


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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
theorem _root_.solution [hF : Fact (IsFixF K F)] {𝔭 : Ideal (𝓞 F)} {k j : ℕ}
    {a : 𝓞 K ⧸ extP K 𝔭 ^ k} (ha : a ∈ idQ K 𝔭 k j) : star a ∈ idQ K 𝔭 k j := by
  obtain ⟨z, hz, rfl⟩ := mem_idQ.mp ha
  rw [star_mk]
  exact mem_idQ.mpr ⟨star z, conjO_mem_pow hF.out 𝔭 j z hz, rfl⟩
end Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
