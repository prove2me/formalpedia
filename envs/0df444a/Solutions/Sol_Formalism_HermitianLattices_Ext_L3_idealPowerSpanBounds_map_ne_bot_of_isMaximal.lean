-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds.map_ne_bot_of_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:53:24.363389+00:00
-- url     : https://prove2.me/submissions/6c8daf00-e887-4aff-8a4f-4ac07eba4ca3

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_StarAlgebraMap
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountPowSuccInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_ne_bot

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
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : extP K 𝔭 ≠ ⊥ := by
  intro h
  apply ne_bot h𝔭
  have h1 : Ideal.comap ι (Ideal.map ι 𝔭) = 𝔭 := Ideal.comap_map_eq_self_of_faithfullyFlat _
  have h3 : Ideal.comap ι (Ideal.map ι (⊥ : Ideal (𝓞 F))) = ⊥ :=
    Ideal.comap_map_eq_self_of_faithfullyFlat _
  rw [Ideal.map_bot] at h3
  change Ideal.map ι 𝔭 = ⊥ at h
  rw [← h1, h, h3]
end Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
