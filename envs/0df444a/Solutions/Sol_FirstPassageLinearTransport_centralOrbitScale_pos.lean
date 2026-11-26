-- Prove2me | solution 1 for FirstPassageLinearTransport.centralOrbitScale_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:01:08.64575+00:00
-- url     : https://prove2.me/submissions/fe819810-dd1c-4d03-aaa9-4bc8bf6820f0

import Mathlib.Algebra.Ring.GeomSum
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_Envelope

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution (k : ℕ) : 0 < centralOrbitScale k := by
  unfold centralOrbitScale
  positivity
end FirstPassageLinearTransport
