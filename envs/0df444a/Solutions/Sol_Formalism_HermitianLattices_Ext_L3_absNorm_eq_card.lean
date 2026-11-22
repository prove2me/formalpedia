-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.absNorm_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:39:27.09481+00:00
-- url     : https://prove2.me/submissions/9e04d025-6e4c-4b52-88dc-22c93facbb66

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSubMemOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K : Type} [Field K] [NumberField K] [StarRing K]
omit [StarRing K]
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution (I : Ideal (𝓞 K)) : Ideal.absNorm I = Nat.card (𝓞 K ⧸ I) := by
  first
  | rfl
  | (rw [Ideal.absNorm_apply]; rfl)
  | (rw [Ideal.absNorm_apply, Submodule.cardQuot_apply])
end Formalism.HermitianLattices.Ext.L3
