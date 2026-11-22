-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.MeanB.algebraMap_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:45:33.35539+00:00
-- url     : https://prove2.me/submissions/1cd8b8be-2bfc-4f29-a1cc-bd294e4a15b6

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulSubOneMemPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_StarAlgebraMap

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.MeanB
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
namespace Formalism.HermitianLattices.Ext.L3.MeanB
theorem _root_.solution (a : 𝓞 F) :
    algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) a) = algebraMap F K (a : F) := rfl
end Formalism.HermitianLattices.Ext.L3.MeanB
