-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:30:01.139752+00:00
-- url     : https://prove2.me/submissions/d314428d-40d8-449e-ab8b-a78ae5e5493b

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
theorem _root_.solution {ϖ : K} (hS : IsLocUnif S ϖ) (k : ℕ) : ϖ ^ k ∈ S := by
  exact S.pow_mem hS.mem k
end Formalism.HermitianLattices.Ext.L3.HU
