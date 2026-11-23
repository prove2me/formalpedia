-- Prove2me | solution 1 for Formalism.ELL.wSeriesSubstUnique_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:26:30.865692+00:00
-- url     : https://prove2.me/submissions/38ad2ed5-3584-455a-a8b6-4e753517bbf7

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Theorems.Thm_Formalism_ELL_WeierstrassSeriesLimit_mv_eq_zero
import Theorems.Thm_Formalism_ELL_WeierstrassSeriesLimit_subst_eq
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
private theorem constantCoeff_subst_eq_zero_elliptic_torsion {w : PowerSeries R} (hw0 : constantCoeff w = 0)
    {σ : Type} (s : MvPowerSeries σ R) (hs : MvPowerSeries.constantCoeff s = 0) :
    MvPowerSeries.constantCoeff (w.subst s) = 0 := by
  have ha := hasSubst_of_constantCoeff_eq_zero_elliptic_torsion hs
  obtain ⟨w₁, hw₁⟩ := X_dvd_iff.mpr hw0
  rw [← substAlgHom_apply' ha, hw₁, map_mul, substAlgHom_X' ha, map_mul, hs, zero_mul]
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
open WeierstrassSeriesLimit
namespace Formalism.ELL
theorem _root_.solution : WSubstUnique.{u} := by
  intro R _ W w hw σ _ s hs
  refine ⟨Formalism.ELL.WeierstrassSeriesLimit.subst_eq W hw s hs, fun v hv hvE => ?_⟩
  have hu := Formalism.ELL.WeierstrassSeriesLimit.subst_eq W hw s hs
  have hu0 : MvPowerSeries.constantCoeff (w.subst s) = 0 := _root_.Formalism.ELL.WeierstrassSeriesLimit.constantCoeff_subst_eq_zero_elliptic_torsion hw.1 s hs
  unfold WEqAt at hu hvE
  simp only [Algebra.smul_def] at hu hvE
  have key : v - w.subst s = (v - w.subst s) *
      (algebraMap R (MvPowerSeries σ R) W.a₁ * s + algebraMap R (MvPowerSeries σ R) W.a₂ * s ^ 2
        + algebraMap R (MvPowerSeries σ R) W.a₃ * (v + w.subst s)
        + algebraMap R (MvPowerSeries σ R) W.a₄ * s * (v + w.subst s)
        + algebraMap R (MvPowerSeries σ R) W.a₆ * (v ^ 2 + v * w.subst s + w.subst s ^ 2)) := by
    linear_combination hvE - hu
  refine sub_eq_zero.mp (Formalism.ELL.WeierstrassSeriesLimit.mv_eq_zero ?_ key)
  simp [hs, hv, hu0]
end Formalism.ELL
