-- Prove2me | solution 1 for FiniteEnergyPlane.isSeqCompact_fastPlaneSet
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-04T23:01:20.457189+00:00
-- url     : https://prove2.me/submissions/39931e1f-c47f-448f-adb1-a30c349ddd6a

import Definitions.Def_FiniteEnergyPlane_Compactness
import Theorems.Thm_FiniteEnergyPlane_exists_subseq_tendsto_of_fastPlaneSet
import Theorems.Thm_FiniteEnergyPlane_isNondegenerate_bridge
import Theorems.Thm_FiniteEnergyPlane_periodicOrbit_bridge
import Theorems.Thm_FiniteEnergyPlane_integral_liouvilleForm_eq



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem isSeqCompact_fastPlaneSet_aux (H₀ : HryniewiczCriterion.R4 → ℝ)
    (hH₀ : HryniewiczCriterion.IsStrictlyStarShapedLevel H₀) :
    let H : V 1 → ℝ := fun y => H₀ (fun k => y (Fin.cast (by norm_num) k))
    ∀ J : V 1 → V 1 →L[ℝ] V 1, IsCompatibleXiStructure H J → ∀ P : ReebOrbit H,
    (∀ (R : HryniewiczCriterion.PeriodicOrbit H₀)
      (Y : ℝ → (HryniewiczCriterion.R4 →L[ℝ] HryniewiczCriterion.R4)),
      HryniewiczCriterion.IsLinearizedFlow H₀ R.x Y →
      (∫ t in (0 : ℝ)..R.T, HryniewiczCriterion.liouvilleForm (R.x t) (deriv R.x t)) ≤ P.T →
      ∀ v : Fin 2 → ℝ, (HryniewiczCriterion.linearizedXiPath H₀ R Y 1).mulVec v = v → v = 0) →
    (∀ (R : HryniewiczCriterion.PeriodicOrbit H₀)
      (Y : ℝ → (HryniewiczCriterion.R4 →L[ℝ] HryniewiczCriterion.R4)),
      HryniewiczCriterion.IsLinearizedFlow H₀ R.x Y →
      (∫ t in (0 : ℝ)..R.T, HryniewiczCriterion.liouvilleForm (R.x t) (deriv R.x t)) ≤ P.T →
      3 ≤ HryniewiczCriterion.czIndexOfPath (HryniewiczCriterion.linearizedXiPath H₀ R Y)) →
    ∀ γ : ℝ, 0 < γ → (∀ Q : ReebOrbit H, Q.T ≤ P.T → γ < Q.T) →
    (∀ Q₁ Q₂ : ReebOrbit H, Q₁.T ≤ P.T → Q₂.T ≤ P.T → Q₁.T ≠ Q₂.T → γ < |Q₁.T - Q₂.T|) →
    ∀ K : Set (V 1), IsCompact K → (0 : V 1) ∉ K → (∀ y ∈ K, proj H y ∉ Set.range P.x) →
    IsSeqCompactCInftyLoc (fastPlaneSet H J P K γ) := by
  intro H J hJ P hnd hcz γ hγ hγ₁ hγ₂ K hK hK0 hcone u hu
  have hH : IsStrictlyStarShapedLevel H := (periodicOrbit_bridge H₀).1.2 hH₀
  have hP : ∀ Q : ReebOrbit H, Q.T ≤ P.T → Q.IsNondegenerate ∧ Q.IsCZAtLeast 3 := by
    intro Q hQ
    obtain ⟨R, hR1, hR2⟩ := ((periodicOrbit_bridge H₀).2 hH₀).2 Q
    refine ⟨(isNondegenerate_bridge H₀ hH₀ R Q hR1.symm hR2).2
      (fun Y hY => hnd R Y hY ((integral_liouvilleForm_eq H₀ R).le.trans
        (hR2.symm.le.trans hQ))), ?_⟩
    intro R' _ hT Y hY
    exact hcz R' Y hY ((integral_liouvilleForm_eq H₀ R').le.trans (hT.symm.le.trans hQ))
  obtain ⟨φ, hφ, Γ, -, w, -, -, -, -, hcase⟩ :=
    exists_subseq_tendsto_of_fastPlaneSet H hH J hJ P hP γ hγ hγ₁ hγ₂ K hK hK0 u hu
  rcases hcase with ⟨-, -, -, y, hy, hyP⟩ | ⟨A, -, -, -, c, -, hconv, hmem, -⟩
  · exact absurd hyP (hcone y hy)
  · exact ⟨φ, hφ, _, hmem, hconv⟩

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H₀ : HryniewiczCriterion.R4 → ℝ)
    (hH₀ : HryniewiczCriterion.IsStrictlyStarShapedLevel H₀) :
    let H : V 1 → ℝ := fun y => H₀ (fun k => y (Fin.cast (by norm_num) k))
    ∀ J : V 1 → V 1 →L[ℝ] V 1, IsCompatibleXiStructure H J → ∀ P : ReebOrbit H,
    (∀ (R : HryniewiczCriterion.PeriodicOrbit H₀)
      (Y : ℝ → (HryniewiczCriterion.R4 →L[ℝ] HryniewiczCriterion.R4)),
      HryniewiczCriterion.IsLinearizedFlow H₀ R.x Y →
      (∫ t in (0 : ℝ)..R.T, HryniewiczCriterion.liouvilleForm (R.x t) (deriv R.x t)) ≤ P.T →
      ∀ v : Fin 2 → ℝ, (HryniewiczCriterion.linearizedXiPath H₀ R Y 1).mulVec v = v → v = 0) →
    (∀ (R : HryniewiczCriterion.PeriodicOrbit H₀)
      (Y : ℝ → (HryniewiczCriterion.R4 →L[ℝ] HryniewiczCriterion.R4)),
      HryniewiczCriterion.IsLinearizedFlow H₀ R.x Y →
      (∫ t in (0 : ℝ)..R.T, HryniewiczCriterion.liouvilleForm (R.x t) (deriv R.x t)) ≤ P.T →
      3 ≤ HryniewiczCriterion.czIndexOfPath (HryniewiczCriterion.linearizedXiPath H₀ R Y)) →
    ∀ γ : ℝ, 0 < γ → (∀ Q : ReebOrbit H, Q.T ≤ P.T → γ < Q.T) →
    (∀ Q₁ Q₂ : ReebOrbit H, Q₁.T ≤ P.T → Q₂.T ≤ P.T → Q₁.T ≠ Q₂.T → γ < |Q₁.T - Q₂.T|) →
    ∀ K : Set (V 1), IsCompact K → (0 : V 1) ∉ K → (∀ y ∈ K, proj H y ∉ Set.range P.x) →
    IsSeqCompactCInftyLoc (fastPlaneSet H J P K γ) :=
  isSeqCompact_fastPlaneSet_aux H₀ hH₀
