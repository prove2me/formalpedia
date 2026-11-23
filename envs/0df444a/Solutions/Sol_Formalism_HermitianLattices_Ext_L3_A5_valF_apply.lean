-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.A5.valF_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:28.456053+00:00
-- url     : https://prove2.me/submissions/95fedc2e-875b-4cab-86da-ab47602abe0c

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFilterResCharLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SummableSqGeom
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FinitePrimesOfMem

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
theorem _root_.solution {n : 𝓞 F} (hn : n ≠ 0) (𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) :
    valF n 𝔭 = vF 𝔭.1 n := by
  unfold valF
  rw [dif_pos hn]
  rfl
end Formalism.HermitianLattices.Ext.L3.A5
