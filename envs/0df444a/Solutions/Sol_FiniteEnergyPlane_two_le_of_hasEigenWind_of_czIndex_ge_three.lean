-- Prove2me | solution 1 for FiniteEnergyPlane.two_le_of_hasEigenWind_of_czIndex_ge_three
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-02T20:11:11.019974+00:00
-- url     : https://prove2.me/submissions/1189116a-adea-4394-a820-bee1d2962cbe

import Definitions.Def_FiniteEnergyPlane_Winding
import Theorems.Thm_FiniteEnergyPlane_czIndexOfPath_eq_alphaMinus_add_alphaPlus
import Theorems.Thm_AsymptoticOperator_linearODE_existsUnique



/-!
# Hryniewicz Lemma 4.5: `μ_CZ ≥ 3` forces windings `≥ 2` for eigenvalues `μ ≥ 0`

Glue of HWZ Thm 3.10 (`czIndexOfPath_eq_alphaMinus_add_alphaPlus`) and the global linear ODE
(`AsymptoticOperator.linearODE_existsUnique`), which supplies a linearized flow `Y`.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

lemma l45_contDiff_hamiltonianVectorField (H₀ : HryniewiczCriterion.R4 → ℝ)
    (hH : ContDiff ℝ ∞ H₀) : ContDiff ℝ 1 (HryniewiczCriterion.hamiltonianVectorField H₀) := by
  have hd : ContDiff ℝ 1 (fderiv ℝ H₀) := hH.fderiv_right (by norm_cast)
  have hp : ∀ i : Fin 4, ContDiff ℝ 1 (fun x => HryniewiczCriterion.partialDeriv H₀ x i) :=
    fun i => hd.clm_apply contDiff_const
  refine contDiff_pi.2 fun i => ?_
  fin_cases i
  · exact (hp 1).neg
  · exact hp 0
  · exact (hp 3).neg
  · exact hp 2

lemma l45_exists_isLinearizedFlow (H₀ : HryniewiczCriterion.R4 → ℝ)
    (hH₀ : HryniewiczCriterion.IsStrictlyStarShapedLevel H₀)
    (P : HryniewiczCriterion.PeriodicOrbit H₀) :
    ∃ Y : ℝ → (HryniewiczCriterion.R4 →L[ℝ] HryniewiczCriterion.R4),
      HryniewiczCriterion.IsLinearizedFlow H₀ P.x Y := by
  have hx : Continuous P.x :=
    continuous_iff_continuousAt.2 fun t => (P.trajectory.1 t).continuousAt
  have hA : Continuous fun t =>
      fderiv ℝ (HryniewiczCriterion.hamiltonianVectorField H₀) (P.x t) :=
    ((l45_contDiff_hamiltonianVectorField H₀ hH₀.1).continuous_fderiv (by simp)).comp hx
  let B : ℝ → ((HryniewiczCriterion.R4 →L[ℝ] HryniewiczCriterion.R4) →L[ℝ]
      (HryniewiczCriterion.R4 →L[ℝ] HryniewiczCriterion.R4)) := fun t =>
    ContinuousLinearMap.compL ℝ HryniewiczCriterion.R4 HryniewiczCriterion.R4
      HryniewiczCriterion.R4 (fderiv ℝ (HryniewiczCriterion.hamiltonianVectorField H₀) (P.x t))
  have hB : Continuous B := (ContinuousLinearMap.compL ℝ HryniewiczCriterion.R4
      HryniewiczCriterion.R4 HryniewiczCriterion.R4).continuous.comp hA
  obtain ⟨Y, ⟨hY0, hY⟩, -⟩ :=
    AsymptoticOperator.linearODE_existsUnique B hB (ContinuousLinearMap.id ℝ _)
  exact ⟨Y, hY0, hY⟩

theorem two_le_of_hasEigenWind_of_czIndex_ge_three_aux (H₀ : HryniewiczCriterion.R4 → ℝ)
    (hH₀ : HryniewiczCriterion.IsStrictlyStarShapedLevel H₀) :
    let toV : HryniewiczCriterion.R4 → V 1 := fun x k => x (Fin.cast (by norm_num) k)
    let H : V 1 → ℝ := fun y => H₀ (fun k => y (Fin.cast (by norm_num) k))
    ∀ J : V 1 → V 1 →L[ℝ] V 1, IsCompatibleXiStructure H J →
    ∀ (P : HryniewiczCriterion.PeriodicOrbit H₀) (Q : ReebOrbit H),
      Set.range Q.x = Set.range (fun τ => toV (P.x τ)) →
      Q.T = ∫ τ in (0 : ℝ)..P.T, liouville (toV (P.x τ)) (deriv (fun s => toV (P.x s)) τ) →
      Q.IsNondegenerate →
      (∀ Y : ℝ → (HryniewiczCriterion.R4 →L[ℝ] HryniewiczCriterion.R4),
        HryniewiczCriterion.IsLinearizedFlow H₀ P.x Y →
        3 ≤ HryniewiczCriterion.czIndexOfPath (HryniewiczCriterion.linearizedXiPath H₀ P Y)) →
      ∀ μ : ℝ, 0 ≤ μ → ∀ k : ℤ, HasEigenWind J Q μ k → 2 ≤ k := by
  intro toV H J hJ P Q hr hT hnd hcz μ hμ k hk
  obtain ⟨a, b, -, hb, hab, hab'⟩ :=
    czIndexOfPath_eq_alphaMinus_add_alphaPlus H₀ hH₀ J hJ P Q hr hT hnd
  obtain ⟨Y, hY⟩ := l45_exists_isLinearizedFlow H₀ hH₀ P
  have h3 := hcz Y hY
  rw [hab' Y hY] at h3
  have hbk := hb.2 μ hμ k hk
  omega

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H₀ : HryniewiczCriterion.R4 → ℝ)
    (hH₀ : HryniewiczCriterion.IsStrictlyStarShapedLevel H₀) :
    let toV : HryniewiczCriterion.R4 → V 1 := fun x k => x (Fin.cast (by norm_num) k)
    let H : V 1 → ℝ := fun y => H₀ (fun k => y (Fin.cast (by norm_num) k))
    ∀ J : V 1 → V 1 →L[ℝ] V 1, IsCompatibleXiStructure H J →
    ∀ (P : HryniewiczCriterion.PeriodicOrbit H₀) (Q : ReebOrbit H),
      Set.range Q.x = Set.range (fun τ => toV (P.x τ)) →
      Q.T = ∫ τ in (0 : ℝ)..P.T, liouville (toV (P.x τ)) (deriv (fun s => toV (P.x s)) τ) →
      Q.IsNondegenerate →
      (∀ Y : ℝ → (HryniewiczCriterion.R4 →L[ℝ] HryniewiczCriterion.R4),
        HryniewiczCriterion.IsLinearizedFlow H₀ P.x Y →
        3 ≤ HryniewiczCriterion.czIndexOfPath (HryniewiczCriterion.linearizedXiPath H₀ P Y)) →
      ∀ μ : ℝ, 0 ≤ μ → ∀ k : ℤ, HasEigenWind J Q μ k → 2 ≤ k :=
  FiniteEnergyPlane.two_le_of_hasEigenWind_of_czIndex_ge_three_aux H₀ hH₀
