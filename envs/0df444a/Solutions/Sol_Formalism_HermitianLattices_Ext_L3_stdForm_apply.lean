-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.stdForm_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:25:39.939208+00:00
-- url     : https://prove2.me/submissions/228a3e9b-c1ca-43fb-86d8-105e7a73f9dd

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassSt
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteDimensionalOfOrtho

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
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution (K : Type) [Field K] [StarRing K] (n : ℕ) (x y : Fin n → K) :
    stdForm K n x y = ∑ i, star (x i) * y i := rfl
end Formalism.HermitianLattices.Ext.L3
