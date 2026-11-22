-- Prove2me | solution 1 for Formalism.GM.ProjS.eulL_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:29:33.785994+00:00
-- url     : https://prove2.me/submissions/b726bb4c-8ad8-4007-b819-34a945bbf019

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.ProjS
open MvPolynomial Finset
variable {k σ : Type} [Field k]
namespace Formalism.GM.ProjS
theorem _root_.solution {s : ℕ} (t : Fin s → σ) (g : MvPolynomial σ k) :
    eulL t g = ∑ c, X (t c) * pderiv (t c) g := by
  simp only [eulL, LinearMap.sum_apply]
  rfl
end Formalism.GM.ProjS
