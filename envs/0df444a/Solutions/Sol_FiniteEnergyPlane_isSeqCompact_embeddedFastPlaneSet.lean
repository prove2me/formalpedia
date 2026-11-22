-- Prove2me | solution 1 for FiniteEnergyPlane.isSeqCompact_embeddedFastPlaneSet
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-21T10:26:05.22321+00:00
-- url     : https://prove2.me/submissions/43a70dfc-d230-4b1f-b004-2341d4f14454

import Definitions.Def_FiniteEnergyPlane_Fredholm
import Theorems.Thm_FiniteEnergyPlane_exists_subseq_tendsto_of_fastPlaneSet
import Theorems.Thm_FiniteEnergyPlane_isEmbeddedPlane_of_tendstoCInftyLocOn



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem isSeqCompact_embeddedFastPlaneSet' (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H)
    (hP : ∀ Q : ReebOrbit H, Q.T ≤ P.T → Q.IsNondegenerate ∧ Q.IsCZAtLeast 3)
    (γ : ℝ) (hγ : 0 < γ) (hγ₁ : ∀ Q : ReebOrbit H, Q.T ≤ P.T → γ < Q.T)
    (hγ₂ : ∀ Q₁ Q₂ : ReebOrbit H, Q₁.T ≤ P.T → Q₂.T ≤ P.T → Q₁.T ≠ Q₂.T → γ < |Q₁.T - Q₂.T|)
    (K : Set (V 1)) (hK : IsCompact K) (hK₀ : (0 : V 1) ∉ K)
    (hKP : ∀ y ∈ K, proj H y ∉ Set.range P.x) :
    IsSeqCompactCInftyLoc (embeddedFastPlaneSet H J P K γ) := by
  intro u hu
  obtain ⟨φ, hφ, Γ, -, w, -, -, -, -, hcase⟩ :=
    exists_subseq_tendsto_of_fastPlaneSet H hH J hJ P hP γ hγ hγ₁ hγ₂ K hK hK₀ u
      (fun k => (hu k).1)
  rcases hcase with ⟨-, -, -, y, hy, hyP⟩ | ⟨A, -, -, -, c, -, hconv, hmem, -⟩
  · exact absurd hyP (hKP y hy)
  · refine ⟨φ, hφ, _, ⟨hmem, ?_⟩, hconv⟩
    exact isEmbeddedPlane_of_tendstoCInftyLocOn H hH J hJ (fun k => u (φ k)) _
      (fun k => (hu (φ k)).1.1) (fun k => (hu (φ k)).2) hmem.1 hconv

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
    (K : Set (V 1)) (hK : IsCompact K) (hK₀ : (0 : V 1) ∉ K)
    (hKP : ∀ y ∈ K, proj H y ∉ Set.range P.x) :
    IsSeqCompactCInftyLoc (embeddedFastPlaneSet H J P K γ) :=
  isSeqCompact_embeddedFastPlaneSet' H hH J hJ P hP γ hγ hγ₁ hγ₂ K hK hK₀ hKP
