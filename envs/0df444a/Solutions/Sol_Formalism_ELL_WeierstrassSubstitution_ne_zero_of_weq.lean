-- Prove2me | solution 1 for Formalism.ELL.WeierstrassSubstitution.ne_zero_of_weq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:24:01.222772+00:00
-- url     : https://prove2.me/submissions/2bb82248-586b-47c8-ac48-0bbebac166d0

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Theorems.Thm_Formalism_ELL_WeierstrassSubstitution_eq_zero_of_weq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.WeierstrassSubstitution
namespace Formalism.ELL.WeierstrassSubstitution
theorem _root_.solution {K : Type u} [Field K] {W : WeierstrassCurve K} {σ : Type}
    {s v : MvPowerSeries σ K} (h : Formalism.ELL.WEqAt W s v) (hs : s ≠ 0) : v ≠ 0 := by
  rintro rfl
  exact hs (eq_zero_of_weq h)
end Formalism.ELL.WeierstrassSubstitution
