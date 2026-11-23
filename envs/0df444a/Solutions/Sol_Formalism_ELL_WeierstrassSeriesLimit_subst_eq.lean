-- Prove2me | solution 1 for Formalism.ELL.WeierstrassSeriesLimit.subst_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:24:08.130084+00:00
-- url     : https://prove2.me/submissions/4a16a8e3-e102-4fdf-90c3-ceaba45d5570

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open PowerSeries
universe u
noncomputable section
namespace Formalism.ELL
namespace WeierstrassSeriesLimit
section Series
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
end Series
section Subst
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
private theorem hasSubst_of_constantCoeff_eq_zero_elliptic_torsion {σ : Type} {s : MvPowerSeries σ R}
    (hs : MvPowerSeries.constantCoeff s = 0) : PowerSeries.HasSubst s :=
  PowerSeries.HasSubst.of_constantCoeff_zero hs
private theorem substAlgHom_apply' {σ : Type} {s : MvPowerSeries σ R} (ha : PowerSeries.HasSubst s)
    (f : PowerSeries R) : PowerSeries.substAlgHom ha f = f.subst s :=
  congrFun (PowerSeries.coe_substAlgHom ha) f
private theorem substAlgHom_X' {σ : Type} {s : MvPowerSeries σ R} (ha : PowerSeries.HasSubst s) :
    PowerSeries.substAlgHom ha (X : PowerSeries R) = s := by
  rw [substAlgHom_apply']
  exact PowerSeries.subst_X ha
private theorem powerSeries_smul_eq_C_mul (r : R) (f : PowerSeries R) : r • f = C r * f :=
  PowerSeries.smul_eq_C_mul f r
private theorem substAlgHom_C {σ : Type} {s : MvPowerSeries σ R} (ha : PowerSeries.HasSubst s)
    (r : R) : PowerSeries.substAlgHom ha (C r) = algebraMap R (MvPowerSeries σ R) r := by
  rw [show (C r : PowerSeries R) = r • (1 : PowerSeries R) by rw [powerSeries_smul_eq_C_mul, mul_one],
    map_smul, map_one, Algebra.smul_def, mul_one]
end Subst
end WeierstrassSeriesLimit
end Formalism.ELL
end
end

set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL
open Formalism.ELL.WeierstrassSeriesLimit
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
namespace Formalism.ELL.WeierstrassSeriesLimit
theorem _root_.solution {w : PowerSeries R} (hw : WFixed W w) {σ : Type} (s : MvPowerSeries σ R)
    (hs : MvPowerSeries.constantCoeff s = 0) : WEqAt W s (w.subst s) := by
  have ha := hasSubst_of_constantCoeff_eq_zero_elliptic_torsion hs
  have e := congrArg (PowerSeries.substAlgHom ha) hw.2
  simp only [map_add, map_mul, map_pow, substAlgHom_C ha, substAlgHom_X' ha] at e
  rw [substAlgHom_apply' ha] at e
  unfold Formalism.ELL.WEqAt
  simp only [Algebra.smul_def]
  linear_combination e
end Formalism.ELL.WeierstrassSeriesLimit
