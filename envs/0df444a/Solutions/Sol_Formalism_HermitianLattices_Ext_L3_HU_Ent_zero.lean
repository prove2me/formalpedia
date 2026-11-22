-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.Ent.zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:32:26.39527+00:00
-- url     : https://prove2.me/submissions/ba8e60d7-8607-4304-aeb3-fd6813e16733

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsLocUnif

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
variable {K : Type*} [Field K] [StarRing K]
variable {S : Subring K} {m n o : Type*}
namespace Formalism.HermitianLattices.Ext.L3.HU
namespace Ent
theorem _root_.solution : Ent S (0 : Matrix m n K) := by
  exact fun _ _ => S.zero_mem
end Ent
end Formalism.HermitianLattices.Ext.L3.HU
