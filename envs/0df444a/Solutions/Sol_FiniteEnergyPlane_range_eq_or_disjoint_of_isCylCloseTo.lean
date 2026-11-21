-- Prove2me | solution 1 for FiniteEnergyPlane.range_eq_or_disjoint_of_isCylCloseTo
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-16T20:19:43.457097+00:00
-- url     : https://prove2.me/submissions/0fae30cd-13a9-4fc2-9e5a-ea11b0c87a2d

import Definitions.Def_FiniteEnergyPlane_CylClose
import Theorems.Thm_FiniteEnergyPlane_exists_tubeGraph_of_isCylCloseTo
import Theorems.Thm_FiniteEnergyPlane_forall_eq_or_forall_ne_of_tubeGraphs



/-!
# D `range_eq_or_disjoint_of_isCylCloseTo` (a0ea0079): glue

Child A gives one tube `Φ` around `u` in which both planes are holomorphic graphs
`fᵢ = Φ ∘ (ψᵢ, vᵢ)`; child B says the second graph lies on the first everywhere or nowhere.
Everywhere: `f₂ = f₁ ∘ ψ₁⁻¹ ∘ ψ₂` with `ψ₁⁻¹ ∘ ψ₂` bijective, so the images are equal.
Nowhere: a common point would give equal tube coordinates by injectivity of `Φ`.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem range_eq_or_disjoint_of_isCylCloseTo_glue (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (hue : IsEmbeddedPlane u) :
    ∃ ε > 0, ∀ f₁ f₂ : ℂ → V 1,
      IsFastPlane H J f₁ → IsNondegenerateEnd H f₁ cylInf P 1 → IsCylCloseTo H ε f₁ u →
      IsFastPlane H J f₂ → IsNondegenerateEnd H f₂ cylInf P 1 → IsCylCloseTo H ε f₂ u →
      Set.range f₁ = Set.range f₂ ∨ Disjoint (Set.range f₁) (Set.range f₂) := by
  obtain ⟨ρ, -, b, hb, Φ, Jbar, Jinf, Sinf, δ, hδ, ε, hε, hT, hinj, hwind, hgraph⟩ :=
    exists_tubeGraph_of_isCylCloseTo H hH J hJ P hcz u hu huP hue
  refine ⟨ε, hε, fun f₁ f₂ hf₁ hf₁P hf₁c hf₂ hf₂P hf₂c => ?_⟩
  obtain ⟨ψ₁, v₁, κ₁, b₁, hψ₁, hψ₁', hv₁, hv₁ρ, hrep₁, hhol₁, hκ₁, hb₁, hψ₁as, hv₁as⟩ :=
    hgraph f₁ hf₁ hf₁P hf₁c
  obtain ⟨ψ₂, v₂, κ₂, b₂, hψ₂, hψ₂', hv₂, hv₂ρ, hrep₂, hhol₂, hκ₂, hb₂, hψ₂as, hv₂as⟩ :=
    hgraph f₂ hf₂ hf₂P hf₂c
  rcases forall_eq_or_forall_ne_of_tubeGraphs ρ b hb Jbar Jinf Sinf hT δ hδ hwind ψ₁ ψ₂ v₁ v₂
      κ₁ κ₂ b₁ b₂ hψ₁ hψ₁' hv₁ hψ₂ hψ₂' hv₂ hv₁ρ hv₂ρ hhol₁ hhol₂ hκ₁ hb₁ hψ₁as hv₁as
      hκ₂ hb₂ hψ₂as hv₂as with heq | hne
  · -- `f₂ = f₁ ∘ φ` with `φ = ψ₁⁻¹ ∘ ψ₂` bijective
    left
    have hcomp : ∀ z, f₂ z = f₁ (ψ₁.symm (ψ₂ z)) := fun z => by
      rw [hrep₂ z, hrep₁ (ψ₁.symm (ψ₂ z)), ψ₁.apply_symm_apply, heq z]
    ext y
    constructor
    · rintro ⟨w, rfl⟩
      refine ⟨ψ₂.symm (ψ₁ w), ?_⟩
      rw [hcomp, ψ₂.apply_symm_apply, ψ₁.symm_apply_apply]
    · rintro ⟨z, rfl⟩
      exact ⟨_, (hcomp z).symm⟩
  · right
    rw [Set.disjoint_left]
    rintro y ⟨z₁, rfl⟩ ⟨z₂, hz₂⟩
    have hmem₁ : (ψ₁ z₁, v₁ z₁) ∈ Set.univ ×ˢ ball (0 : ℂ) ρ := ⟨trivial, hv₁ρ z₁⟩
    have hmem₂ : (ψ₂ z₂, v₂ z₂) ∈ Set.univ ×ˢ ball (0 : ℂ) ρ := ⟨trivial, hv₂ρ z₂⟩
    have hΦ : Φ (ψ₂ z₂, v₂ z₂) = Φ (ψ₁ z₁, v₁ z₁) := by rw [← hrep₂, ← hrep₁, hz₂]
    have hp := hinj hmem₂ hmem₁ hΦ
    simp only [Prod.mk.injEq] at hp
    obtain ⟨h1, h2⟩ := hp
    apply hne z₂
    rw [h1, ψ₁.symm_apply_apply, h2]

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (hue : IsEmbeddedPlane u) :
    ∃ ε > 0, ∀ f₁ f₂ : ℂ → V 1,
      IsFastPlane H J f₁ → IsNondegenerateEnd H f₁ cylInf P 1 → IsCylCloseTo H ε f₁ u →
      IsFastPlane H J f₂ → IsNondegenerateEnd H f₂ cylInf P 1 → IsCylCloseTo H ε f₂ u →
      Set.range f₁ = Set.range f₂ ∨ Disjoint (Set.range f₁) (Set.range f₂) :=
  range_eq_or_disjoint_of_isCylCloseTo_glue H hH J hJ P hcz u hu huP hue
