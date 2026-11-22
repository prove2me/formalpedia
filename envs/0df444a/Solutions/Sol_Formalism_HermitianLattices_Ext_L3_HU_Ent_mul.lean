-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.Ent.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:32:20.958675+00:00
-- url     : https://prove2.me/submissions/ae8ebc98-a102-40b8-912d-f1c394bbf0e4

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
theorem _root_.solution [Fintype n] {M : Matrix m n K} {N : Matrix n o K} (hM : Ent S M) (hN : Ent S N) :
    Ent S (M * N) := by
  intro i j
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => S.mul_mem (hM i k) (hN k j)
end Ent
end Formalism.HermitianLattices.Ext.L3.HU
