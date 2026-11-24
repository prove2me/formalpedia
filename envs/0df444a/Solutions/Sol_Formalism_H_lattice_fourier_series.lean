-- Prove2me | solution 1 for Formalism.H.lattice_fourier_series
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:22.332724+00:00
-- url     : https://prove2.me/submissions/a9e013ab-389e-4dc0-9607-c6be7e5dadfc

import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_TorusProjIsOpenQuotientMap
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_LatticeFourierSeries
import Theorems.Thm_Formalism_H_coeff_integrand_periodic
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_H_integral_fundamentalDomain_eq
import Theorems.Thm_Formalism_H_mFourierCoeff_torusFunC
import Theorems.Thm_Formalism_H_mFourier_torusProj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open MeasureTheory Set Complex
open scoped RealInnerProductSpace
noncomputable section
open Formalism Formalism.H
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
namespace Formalism.H
theorem _root_.solution (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] : LatticeFourierSeries V := by
  intro Λ _ _ G hG hper D hD hsum x
  classical
  have : Module.Free ℤ Λ := ZLattice.module_free ℝ Λ
  have : Module.Finite ℤ Λ := ZLattice.module_finite ℝ Λ
  let b := Module.Free.chooseBasis ℤ Λ
  let e := b.ofZLatticeBasis ℝ Λ
  have he : Submodule.span ℤ (Set.range e) = Λ := b.ofZLatticeBasis_span ℝ Λ
  have hper' : ∀ l ∈ Submodule.span ℤ (Set.range e), ∀ x, G (l + x) = G x := by
    intro l hl x
    rw [he] at hl
    exact hper ⟨l, hl⟩ x
  set c : V → ℂ := fun μ =>
    ∫ y in D, G y * Complex.exp (-(2 * Real.pi * Complex.I * (⟪μ, y⟫ : ℝ))) with hc
  have hF : IsAddFundamentalDomain Λ (ZSpan.fundamentalDomain e) volume := by
    have h := ZSpan.isAddFundamentalDomain e volume
    rw [he] at h
    exact h
  have : MeasurableVAdd Λ V := (inferInstance : MeasurableVAdd Λ.toAddSubgroup V)
  have : VAddInvariantMeasure Λ V volume :=
    (inferInstance : VAddInvariantMeasure Λ.toAddSubgroup V volume)
  have hcov : ZLattice.covolume Λ = volume.real (ZSpan.fundamentalDomain e) :=
    ZLattice.covolume_eq_measure_fundamentalDomain Λ volume hF
  have hcov0 : (ZLattice.covolume Λ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (ZLattice.covolume_ne_zero Λ volume)
  let g := torusFunC e G hG hper'
  have hmem : ∀ m, dualVec e m ∈ dual Λ := fun m => by
    have h := dualVec_mem e m
    rw [he] at h
    exact h
  have hcoef : ∀ m, c (dualVec e m) = (ZLattice.covolume Λ : ℂ) * UnitAddTorus.mFourierCoeff g m := by
    intro m
    simp only [hc]
    rw [hD.setIntegral_eq hF (fun l y => coeff_integrand_periodic Λ G hper _ (hmem m) l y),
      integral_fundamentalDomain_eq, hcov, mFourierCoeff_torusFunC]
  let E : (Module.Free.ChooseBasisIndex ℤ Λ → ℤ) ≃ dual Λ := (dualEquiv e).trans (Equiv.subtypeEquivRight (fun v => by rw [he]))
  have hE : ∀ m, ((E m : dual Λ) : V) = dualVec e m := fun m => rfl
  have hsumE : Summable (fun m => c (dualVec e m)) := by
    have := (E.summable_iff (f := fun μ : dual Λ => c μ)).2 hsum
    exact this
  have hsg : Summable (UnitAddTorus.mFourierCoeff g) := by
    refine (hsumE.mul_left ((ZLattice.covolume Λ : ℂ)⁻¹)).congr fun m => ?_
    rw [hcoef, ← mul_assoc, inv_mul_cancel₀ hcov0, one_mul]
  have hx := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hsg
    (torusProj _ (e.equivFunL x))
  have hgx : g (torusProj _ (e.equivFunL x)) = G x := by
    show torusFun e G _ = _
    rw [torusFun_proj e G hper', ContinuousLinearEquiv.symm_apply_apply]
  rw [hgx] at hx
  rw [← E.hasSum_iff]
  convert hx using 1
  funext m
  simp only [Function.comp_apply, hE, smul_eq_mul, mFourier_torusProj e,
    ContinuousLinearEquiv.symm_apply_apply]
  have := hcoef m
  simp only [hc] at this
  rw [this, ← mul_assoc, inv_mul_cancel₀ hcov0, one_mul]
end Formalism.H
