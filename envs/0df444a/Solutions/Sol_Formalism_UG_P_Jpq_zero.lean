-- Prove2me | solution 1 for Formalism.UG.P.Jpq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:54:12.710405+00:00
-- url     : https://prove2.me/submissions/93d3035f-8e07-4307-9193-59565c01e39f

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Upqcpt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution (p : ℕ) : Formalism.UG.Jpq p 0 = 1 := by
  unfold Formalism.UG.Jpq
  rw [← Matrix.fromBlocks_one]
  congr 1
  ext i j
  exact i.elim0
end Formalism.UG.P
