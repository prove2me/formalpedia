-- Prove2me | solution 1 for Formalism.UG.P.cartan_det_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:35.648855+00:00
-- url     : https://prove2.me/submissions/f6c9d406-262a-4817-8dbb-6d005e100621

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Cartan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] (O : Subring L) {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution (M : Matrix n n L) (hM : ∀ i j, M i j ∈ O) : M.det ∈ O := by
  rw [Matrix.det_apply]
  refine sum_mem (fun σ _ => ?_)
  rw [Units.smul_def]
  exact zsmul_mem (prod_mem fun i _ => hM _ _) _
end Formalism.UG.P
