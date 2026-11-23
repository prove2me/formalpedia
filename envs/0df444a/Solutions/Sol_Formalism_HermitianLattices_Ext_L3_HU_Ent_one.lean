-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.Ent.one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:51:49.347101+00:00
-- url     : https://prove2.me/submissions/449d0f51-b1a5-4e6d-8581-39ef71904498

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
theorem _root_.solution [DecidableEq n] : Ent S (1 : Matrix n n K) := by
  intro i j
  rw [Matrix.one_apply]
  split_ifs
  · exact S.one_mem
  · exact S.zero_mem
end Ent
end Formalism.HermitianLattices.Ext.L3.HU
