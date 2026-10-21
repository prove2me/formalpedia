-- Prove2me | solution 1 for CauchyRiemannIndex.index_eq_winding_of_antilinear_deformation
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-17T14:52:16.207081+00:00
-- url     : https://prove2.me/submissions/5ad3ece8-852a-4b93-a1d6-7cfbb6fe8b23

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Theorems.Thm_CauchyRiemannIndex_crIndex_eq_of_asymptoticCZIndex_eq
import Theorems.Thm_CauchyRiemannIndex_exists_asymptotic_crIndex_eq_sub
import Theorems.Thm_CauchyRiemannIndex_asymptoticCZIndex_eq_winding_of_antilinear



namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

theorem index_eq_winding_of_antilinear_deformation_aux (Splus Sminus : ℝ → Mat 1)
    (hSplus : IsSymLoop Splus) (hSminus : IsSymLoop Sminus)
    (hplus : IsNondegenerate Splus) (hminus : IsNondegenerate Sminus)
    (S : ℝ × ℝ → Mat 1) (hS : IsAsymptoticTo S Splus Sminus)
    (S'plus S'minus : ℝ → Mat 1) (h'plus : IsSymLoop S'plus) (h'minus : IsSymLoop S'minus)
    (hμplus : asymptoticCZIndex S'plus = asymptoticCZIndex Splus)
    (hμminus : asymptoticCZIndex S'minus = asymptoticCZIndex Sminus)
    (βplus βminus : ℝ → ℂ) (hβplus : Continuous βplus) (hβminus : Continuous βminus)
    (hperplus : Function.Periodic βplus 1) (hperminus : Function.Periodic βminus 1)
    (hnzplus : ∀ t, βplus t ≠ 0) (hnzminus : ∀ t, βminus t ≠ 0)
    (hndplus : ∀ σ : ℝ, 0 ≤ σ → IsNondegenerate (fun t => S'plus t + σ • antilinearMat (βplus t)))
    (hndminus : ∀ σ : ℝ, 0 ≤ σ → IsNondegenerate (fun t => S'minus t + σ • antilinearMat (βminus t)))
    (wplus wminus : ℤ) (θplus θminus : ℝ → ℝ) (hθplus : Continuous θplus)
    (hθminus : Continuous θminus)
    (hargplus : ∀ t, βplus t = ‖βplus t‖ * Complex.exp (θplus t * Complex.I))
    (hargminus : ∀ t, βminus t = ‖βminus t‖ * Complex.exp (θminus t * Complex.I))
    (hwplus : θplus 1 - θplus 0 = 2 * Real.pi * wplus)
    (hwminus : θminus 1 - θminus 0 = 2 * Real.pi * wminus) :
    crIndex 2 S = wplus - wminus := by
  have hp : asymptoticCZIndex Splus = wplus := by
    rw [← hμplus]
    exact asymptoticCZIndex_eq_winding_of_antilinear S'plus h'plus βplus hβplus hperplus hnzplus
      hndplus wplus θplus hθplus hargplus hwplus
  have hm : asymptoticCZIndex Sminus = wminus := by
    rw [← hμminus]
    exact asymptoticCZIndex_eq_winding_of_antilinear S'minus h'minus βminus hβminus hperminus
      hnzminus hndminus wminus θminus hθminus hargminus hwminus
  obtain ⟨T, Tplus, Tminus, hTp, hTm, hnTp, hnTm, hμTp, hμTm, hT, hidx⟩ :=
    exists_asymptotic_crIndex_eq_sub wplus wminus
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  rw [crIndex_eq_of_asymptoticCZIndex_eq 1 2 (by norm_num) (by norm_num) Splus Sminus Tplus Tminus
    hSplus hSminus hTp hTm hplus hminus hnTp hnTm (hp.trans hμTp.symm) (hm.trans hμTm.symm)
    S T hS hT, hidx]

end CauchyRiemannIndex

open CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

theorem solution (Splus Sminus : ℝ → Mat 1)
    (hSplus : IsSymLoop Splus) (hSminus : IsSymLoop Sminus)
    (hplus : IsNondegenerate Splus) (hminus : IsNondegenerate Sminus)
    (S : ℝ × ℝ → Mat 1) (hS : IsAsymptoticTo S Splus Sminus)
    (S'plus S'minus : ℝ → Mat 1) (h'plus : IsSymLoop S'plus) (h'minus : IsSymLoop S'minus)
    (hμplus : asymptoticCZIndex S'plus = asymptoticCZIndex Splus)
    (hμminus : asymptoticCZIndex S'minus = asymptoticCZIndex Sminus)
    (βplus βminus : ℝ → ℂ) (hβplus : Continuous βplus) (hβminus : Continuous βminus)
    (hperplus : Function.Periodic βplus 1) (hperminus : Function.Periodic βminus 1)
    (hnzplus : ∀ t, βplus t ≠ 0) (hnzminus : ∀ t, βminus t ≠ 0)
    (hndplus : ∀ σ : ℝ, 0 ≤ σ → IsNondegenerate (fun t => S'plus t + σ • antilinearMat (βplus t)))
    (hndminus : ∀ σ : ℝ, 0 ≤ σ → IsNondegenerate (fun t => S'minus t + σ • antilinearMat (βminus t)))
    (wplus wminus : ℤ) (θplus θminus : ℝ → ℝ) (hθplus : Continuous θplus)
    (hθminus : Continuous θminus)
    (hargplus : ∀ t, βplus t = ‖βplus t‖ * Complex.exp (θplus t * Complex.I))
    (hargminus : ∀ t, βminus t = ‖βminus t‖ * Complex.exp (θminus t * Complex.I))
    (hwplus : θplus 1 - θplus 0 = 2 * Real.pi * wplus)
    (hwminus : θminus 1 - θminus 0 = 2 * Real.pi * wminus) :
    crIndex 2 S = wplus - wminus :=
  CauchyRiemannIndex.index_eq_winding_of_antilinear_deformation_aux Splus Sminus hSplus hSminus hplus hminus S hS S'plus S'minus h'plus h'minus hμplus hμminus βplus βminus hβplus hβminus hperplus hperminus hnzplus hnzminus hndplus hndminus wplus wminus θplus θminus hθplus hθminus hargplus hargminus hwplus hwminus
