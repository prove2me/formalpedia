-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.Ent.conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:42:33.098749+00:00
-- url     : https://prove2.me/submissions/79df3aa8-8de2-45ec-b331-57563bc81c9a

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
theorem _root_.solution (hS : ∀ a ∈ S, star a ∈ S) {M : Matrix m n K} (hM : Ent S M) : Ent S Mᴴ := by
  exact fun i j => hS _ (hM j i)
end Ent
end Formalism.HermitianLattices.Ext.L3.HU
