-- Prove2me | solution 1 for Formalism.ELL.WeierstrassChordSeries.v_ne_of_G
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:25:37.989863+00:00
-- url     : https://prove2.me/submissions/4962219c-8608-467e-aa56-fa81cbd195d2

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_G_zero

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
local notation "L" i => MvPowerSeries.coeff (Finsupp.single i 1)
local notation "cc" => MvPowerSeries.constantCoeff
variable (W : WeierstrassCurve K) (w : PowerSeries K)
variable {W w}
namespace Formalism.ELL.WeierstrassChordSeries
theorem _root_.solution (W : WeierstrassCurve K) {z v : MvPowerSeries (Fin 2) K} (hz : z ≠ 0)
    (hG : G (ca W.a₁) (ca W.a₂) (ca W.a₃) (ca W.a₄) (ca W.a₆) z v = 0) : v ≠ 0 := by
  rintro rfl
  rw [G_zero] at hG
  first
    | exact hz (pow_eq_zero_iff (by norm_num) |>.mp hG)
    | exact hz (pow_eq_zero hG)
end Formalism.ELL.WeierstrassChordSeries
