-- Prove2me | solution 1 for Formalism.G.LogCR.pderiv_subst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:15.907842+00:00
-- url     : https://prove2.me/submissions/6ebae033-968e-4d52-82f1-b03a065ac2e6

import Mathlib
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Theorems.Thm_Formalism_G_LogCR_Agree_mono
import Theorems.Thm_Formalism_G_LogCR_Agree_mul
import Theorems.Thm_Formalism_G_LogCR_agree_truncTotal
import Theorems.Thm_Formalism_G_LogCR_pderiv_aeval

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open Formalism Formalism.G Formalism.G.LogCR
variable {R : Type*} [CommRing R] {σ τ : Type*}
namespace Formalism.G.LogCR
theorem _root_.solution [Fintype σ] [Finite τ] {a : σ → MvPowerSeries τ R}
    (ha : ∀ j, constantCoeff (a j) = 0) (f : MvPowerSeries σ R) (i : τ) :
    MvPowerSeries.pderiv R i (f.subst a) =
      ∑ j, (MvPowerSeries.pderiv R j f).subst a * MvPowerSeries.pderiv R i (a j) := by
  classical
  ext d
  set N := d.degree + 2 with hN
  set P : MvPolynomial σ R := truncTotal N f with hP
  set A : σ → MvPowerSeries τ R := fun j => (truncTotal N (a j) : MvPowerSeries τ R) with hA
  have hA0 : ∀ j, constantCoeff (A j) = 0 := fun j => by
    have := agree_truncTotal N (a j) 0 (by simp [hN])
    rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, ha j] at this
    exact this.symm
  have hfP : Agree N f (P : MvPowerSeries σ R) := agree_truncTotal N f
  have haA : ∀ j, Agree N (a j) (A j) := fun j => agree_truncTotal N (a j)
  have h1 : Agree (d.degree + 1) (MvPowerSeries.pderiv R i (f.subst a))
      (MvPowerSeries.pderiv R i ((P : MvPowerSeries σ R).subst A)) :=
    (Agree.subst ha hA0 hfP haA).pderiv i
  have h2 : ∀ j, Agree (d.degree + 1)
      ((MvPowerSeries.pderiv R j f).subst a * MvPowerSeries.pderiv R i (a j))
      ((MvPowerSeries.pderiv R j (P : MvPowerSeries σ R)).subst A *
        MvPowerSeries.pderiv R i (A j)) := fun j =>
    Agree.mul (Agree.subst ha hA0 (hfP.pderiv j) fun k => (haA k).mono (by omega))
      ((haA j).pderiv i)
  have key : MvPowerSeries.pderiv R i ((P : MvPowerSeries σ R).subst A) =
      ∑ j, (MvPowerSeries.pderiv R j (P : MvPowerSeries σ R)).subst A *
        MvPowerSeries.pderiv R i (A j) := by
    rw [subst_coe, pderiv_aeval]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [MvPowerSeries.pderiv_coe P, subst_coe]
  rw [h1 d (by omega), key, map_sum, map_sum]
  exact Finset.sum_congr rfl fun j _ => (h2 j d (by omega)).symm
end Formalism.G.LogCR
