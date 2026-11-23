-- Prove2me | solution 1 for Formalism.ELL.WeierstrassChordSeries.weq_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:21:16.175368+00:00
-- url     : https://prove2.me/submissions/fe2d594f-28a3-4392-af46-40017a5c21f7

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
local notation "L" i => MvPowerSeries.coeff (Finsupp.single i 1)
local notation "cc" => MvPowerSeries.constantCoeff
variable (W : WeierstrassCurve K) (w : PowerSeries K)
variable {W w}
namespace Formalism.ELL.WeierstrassChordSeries
theorem _root_.solution (W : WeierstrassCurve K) (s v : MvPowerSeries (Fin 2) K) :
    WEqAt W s v ↔ G (ca W.a₁) (ca W.a₂) (ca W.a₃) (ca W.a₄) (ca W.a₆) s v = 0 := by
  unfold Formalism.ELL.WEqAt G
  first
    | (simp only [MvPowerSeries.smul_eq_C_mul]
       rw [sub_eq_zero, eq_comm])
    | (simp only [Algebra.smul_def, MvPowerSeries.algebraMap_apply, Algebra.id.map_eq_id, RingHom.id_apply]
       rw [sub_eq_zero, eq_comm])
end Formalism.ELL.WeierstrassChordSeries
