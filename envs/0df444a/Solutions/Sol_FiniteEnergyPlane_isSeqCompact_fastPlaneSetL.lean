-- Prove2me | solution 1 for FiniteEnergyPlane.isSeqCompact_fastPlaneSetL
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-04T22:45:29.659092+00:00
-- url     : https://prove2.me/submissions/9f10614e-d60a-4282-abaf-b744f01537d0

import Definitions.Def_FiniteEnergyPlane_Compactness
import Theorems.Thm_FiniteEnergyPlane_exists_subseq_tendsto_of_fastPlaneSet



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem isSeqCompact_fastPlaneSetL_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H)
    (hP : ∀ Q : ReebOrbit H, Q.T ≤ P.T → Q.IsNondegenerate ∧ Q.IsCZAtLeast 3)
    (γ : ℝ) (hγ : 0 < γ) (hγ₁ : ∀ Q : ReebOrbit H, Q.T ≤ P.T → γ < Q.T)
    (hγ₂ : ∀ Q₁ Q₂ : ReebOrbit H, Q₁.T ≤ P.T → Q₂.T ≤ P.T → Q₁.T ≠ Q₂.T → γ < |Q₁.T - Q₂.T|)
    (K : Set (V 1)) (hK : IsCompact K) (hK0 : (0 : V 1) ∉ K) (L : ℝ) :
    IsSeqCompactCInftyLoc (fastPlaneSetL H J P K γ L) := by
  intro u hu
  obtain ⟨φ, hφ, Γ, -, w, -, -, -, -, hcase⟩ :=
    exists_subseq_tendsto_of_fastPlaneSet H hH J hJ P hP γ hγ hγ₁ hγ₂ K hK hK0 u
      (fun k => (hu k).1)
  rcases hcase with ⟨hbot, -⟩ | ⟨A, -, hup, -, c, -, hconv, hmem, hA⟩
  · obtain ⟨k, z, hz⟩ := (hbot (-L - 1)).exists
    have := (hu (φ k)).2 z
    linarith
  · refine ⟨φ, hφ, _, ⟨hmem, fun z => ?_⟩, hconv⟩
    have hAL : -L ≤ A := by
      refine le_of_forall_pos_lt_add fun ε hε => ?_
      obtain ⟨k, z', hz'⟩ := (hup (ε / 2) (half_pos hε)).exists
      have := (hu (φ k)).2 z'
      linarith
    exact hAL.trans (hA z)

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H)
    (hP : ∀ Q : ReebOrbit H, Q.T ≤ P.T → Q.IsNondegenerate ∧ Q.IsCZAtLeast 3)
    (γ : ℝ) (hγ : 0 < γ) (hγ₁ : ∀ Q : ReebOrbit H, Q.T ≤ P.T → γ < Q.T)
    (hγ₂ : ∀ Q₁ Q₂ : ReebOrbit H, Q₁.T ≤ P.T → Q₂.T ≤ P.T → Q₁.T ≠ Q₂.T → γ < |Q₁.T - Q₂.T|)
    (K : Set (V 1)) (hK : IsCompact K) (hK0 : (0 : V 1) ∉ K) (L : ℝ) :
    IsSeqCompactCInftyLoc (fastPlaneSetL H J P K γ L) :=
  isSeqCompact_fastPlaneSetL_aux H hH J hJ P hP γ hγ hγ₁ hγ₂ K hK hK0 L
