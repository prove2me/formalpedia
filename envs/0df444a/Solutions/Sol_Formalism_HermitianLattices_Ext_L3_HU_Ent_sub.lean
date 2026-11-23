-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.Ent.sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:08:35.130654+00:00
-- url     : https://prove2.me/submissions/0057ce18-0117-4dae-bd22-a65d9a2bf15d

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
theorem _root_.solution {M N : Matrix m n K} (hM : Ent S M) (hN : Ent S N) : Ent S (M - N) := by
  exact fun i j => S.sub_mem (hM i j) (hN i j)
end Ent
end Formalism.HermitianLattices.Ext.L3.HU
