-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.A5.bId_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:06:32.497823+00:00
-- url     : https://prove2.me/submissions/a645daaa-e66b-47e4-a039-768e9b22768f

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFilterResCharLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SummableSqGeom
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FinitePrimesOfMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_ne_bot_of_max

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.A5
variable {F : Type} [Field F] [NumberField F]
namespace Formalism.HermitianLattices.Ext.L3.A5
theorem _root_.solution (v : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} →₀ ℕ) : bId v ≠ ⊥ := by
  unfold bId Finsupp.prod
  rw [← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
  exact fun 𝔭 _ => pow_ne_zero _ (ne_bot_of_max 𝔭.2)
end Formalism.HermitianLattices.Ext.L3.A5
