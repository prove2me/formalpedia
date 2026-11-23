-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds.piQ_star
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:25:20.027621+00:00
-- url     : https://prove2.me/submissions/8da34851-1a5b-4268-81f5-51605d40d708

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardLiftMatrix
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardQuotExtPPow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_star_mk
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_piQ_mk

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
theorem _root_.solution [Fact (IsFixF K F)] (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : 𝓞 K ⧸ extP K 𝔭 ^ (k + 1)) :
    piQ K 𝔭 k (star a) = star (piQ K 𝔭 k a) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [star_mk, piQ_mk, piQ_mk, star_mk]
end Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
