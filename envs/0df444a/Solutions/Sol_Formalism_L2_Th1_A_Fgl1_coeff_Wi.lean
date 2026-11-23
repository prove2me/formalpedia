-- Prove2me | solution 1 for Formalism.L2.Th1.A.Fgl1.coeff_Wi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:13:28.646674+00:00
-- url     : https://prove2.me/submissions/204816bd-1f88-4eb1-b985-719f4ccc3966

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.Fgl1
local notation "L" i => MvPowerSeries.coeff (Finsupp.single i 1)
local notation "cc" => MvPowerSeries.constantCoeff
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
namespace Formalism.L2.Th1.A.Fgl1
theorem _root_.solution (i : Fin 2) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (Wi W i)
      = if e = Finsupp.single i (e i) then coeff (e i) (wSer W) else 0 := by
  classical
  show MvPowerSeries.coeff e ((wSer W).subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) R)) = _
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.X i), finsum_eq_single _ (e i)]
  · simp only [MvPowerSeries.coeff_X_pow, smul_eq_mul]
    split_ifs <;> simp
  · intro d hd
    simp only [MvPowerSeries.coeff_X_pow]
    rw [if_neg]
    · simp
    · intro h
      apply hd
      rw [h]
      simp
end Formalism.L2.Th1.A.Fgl1
