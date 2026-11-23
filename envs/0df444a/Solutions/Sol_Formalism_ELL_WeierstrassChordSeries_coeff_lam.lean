-- Prove2me | solution 1 for Formalism.ELL.WeierstrassChordSeries.coeff_lam
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:12:17.12595+00:00
-- url     : https://prove2.me/submissions/7751c948-43a6-46dc-9a0d-a161fc9aa23b

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord

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
open Formalism Formalism.ELL
open Formalism.ELL.WeierstrassChordSeries
variable {K : Type u} [Field K]
namespace Formalism.ELL.WeierstrassChordSeries
theorem _root_.solution (w : PowerSeries K) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (lam w) = coeff (e 0 + e 1 + 1) w := rfl
end Formalism.ELL.WeierstrassChordSeries
