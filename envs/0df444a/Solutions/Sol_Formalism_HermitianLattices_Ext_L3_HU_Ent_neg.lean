-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.Ent.neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:27:10.837321+00:00
-- url     : https://prove2.me/submissions/8f84b23f-6f34-4429-aa0f-7cf37ae46405

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
theorem _root_.solution {M : Matrix m n K} (hM : Ent S M) : Ent S (-M) := by
  exact fun i j => S.neg_mem (hM i j)
end Ent
end Formalism.HermitianLattices.Ext.L3.HU
