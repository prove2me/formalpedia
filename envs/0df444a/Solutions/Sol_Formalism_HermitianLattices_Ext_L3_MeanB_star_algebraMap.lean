-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.MeanB.star_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:47:18.597801+00:00
-- url     : https://prove2.me/submissions/47b8f976-0c72-4c03-ac39-35d03324f482

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
theorem _root_.solution (hF : IsFixF K F) (a : F) : star (algebraMap F K a) = algebraMap F K a :=
  (hF _).2 ⟨a, rfl⟩
end Formalism.HermitianLattices.Ext.L3.MeanB
