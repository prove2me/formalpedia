-- Prove2me | solution 1 for FiniteEnergyPlane.exists_fastPlane_open_book
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-25T16:16:57.494048+00:00
-- url     : https://prove2.me/submissions/b8dfec26-1cf5-46cf-a3e5-ce78112ae56b

import Definitions.Def_FiniteEnergyPlane_OpenBook
import Theorems.Thm_FiniteEnergyPlane_periodicOrbit_bridge
import Theorems.Thm_FiniteEnergyPlane_exists_trajectory_return
import Theorems.Thm_FiniteEnergyPlane_exists_page_foliation
import Theorems.Thm_FiniteEnergyPlane_exists_plane_open_book_of_page_foliation
import Theorems.Thm_FiniteEnergyPlane_exists_hit_of_isPlaneOpenBook



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem exists_fastPlane_open_book_aux (H₀ : HryniewiczCriterion.R4 → ℝ)
    (hH₀ : HryniewiczCriterion.IsStrictlyStarShapedLevel H₀) :
    let H : V 1 → ℝ := fun y => H₀ (fun k => y (Fin.cast (by norm_num) k))
    ∀ J : V 1 → V 1 →L[ℝ] V 1, IsCompatibleXiStructure H J → ∀ P : ReebOrbit H,
    P.IsCZAtLeast 3 → (∀ Q : ReebOrbit H, Q.T ≤ P.T → Q.IsNondegenerate) →
    ∀ γ : ℝ, 0 < γ → (∀ Q : ReebOrbit H, Q.T ≤ P.T → γ < Q.T) →
    (∀ Q₁ Q₂ : ReebOrbit H, Q₁.T ≤ P.T → Q₂.T ≤ P.T → Q₁.T ≠ Q₂.T → γ < |Q₁.T - Q₂.T|) →
    (∀ K : Set (V 1), IsCompact K → (0 : V 1) ∉ K → (∀ y ∈ K, proj H y ∉ Set.range P.x) →
      IsSeqCompactCInftyLoc (embeddedFastPlaneSet H J P K γ)) →
    ∀ u₀ : ℂ → V 1, IsFastPlane H J u₀ → IsNondegenerateEnd H u₀ cylInf P 1 → IsEmbeddedPlane u₀ →
    ∀ l : ℕ, 1 ≤ l → ∃ U : ℝ × ℂ → V 1, IsPlaneOpenBook H J P l U ∧
      ∀ y : ℝ → V 1, IsReebTrajectory H y → y 0 ∉ Set.range P.x → ∀ θ n : ℝ,
      (∃ t > n, y t ∈ Set.range (fun z => pageMap H U (θ, z))) ∧
      (∃ t < n, y t ∈ Set.range (fun z => pageMap H U (θ, z))) := by
  intro H J hJ P hcz hnd γ hγ hγ₁ hγ₂ hΛ u₀ h₁ h₂ h₃ l hl
  have hH : IsStrictlyStarShapedLevel H := (periodicOrbit_bridge H₀).1.2 hH₀
  obtain ⟨y, hy, v, hv, τ, hτ, hret⟩ :=
    exists_trajectory_return H hH J hJ P hcz γ hγ (hγ₁ P le_rfl) hΛ u₀ h₁ h₂ h₃
  obtain ⟨L, hL, δ, hδ, U, hU, -⟩ :=
    exists_page_foliation H hH J hJ P hcz hnd γ hγ hγ₁ hγ₂ hΛ y hy v hv τ hτ hret l hl
  obtain ⟨W, hW⟩ :=
    exists_plane_open_book_of_page_foliation H hH J hJ P hcz γ y hy l hl L δ hL hδ U hU
  exact ⟨W, hW, fun y' hy' hy₀ θ n =>
    exists_hit_of_isPlaneOpenBook H hH J hJ P hcz hnd l hl W hW y' hy' hy₀ θ n⟩

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H₀ : HryniewiczCriterion.R4 → ℝ)
    (hH₀ : HryniewiczCriterion.IsStrictlyStarShapedLevel H₀) :
    let H : V 1 → ℝ := fun y => H₀ (fun k => y (Fin.cast (by norm_num) k))
    ∀ J : V 1 → V 1 →L[ℝ] V 1, IsCompatibleXiStructure H J → ∀ P : ReebOrbit H,
    P.IsCZAtLeast 3 → (∀ Q : ReebOrbit H, Q.T ≤ P.T → Q.IsNondegenerate) →
    ∀ γ : ℝ, 0 < γ → (∀ Q : ReebOrbit H, Q.T ≤ P.T → γ < Q.T) →
    (∀ Q₁ Q₂ : ReebOrbit H, Q₁.T ≤ P.T → Q₂.T ≤ P.T → Q₁.T ≠ Q₂.T → γ < |Q₁.T - Q₂.T|) →
    (∀ K : Set (V 1), IsCompact K → (0 : V 1) ∉ K → (∀ y ∈ K, proj H y ∉ Set.range P.x) →
      IsSeqCompactCInftyLoc (embeddedFastPlaneSet H J P K γ)) →
    ∀ u₀ : ℂ → V 1, IsFastPlane H J u₀ → IsNondegenerateEnd H u₀ cylInf P 1 → IsEmbeddedPlane u₀ →
    ∀ l : ℕ, 1 ≤ l → ∃ U : ℝ × ℂ → V 1, IsPlaneOpenBook H J P l U ∧
      ∀ y : ℝ → V 1, IsReebTrajectory H y → y 0 ∉ Set.range P.x → ∀ θ n : ℝ,
      (∃ t > n, y t ∈ Set.range (fun z => pageMap H U (θ, z))) ∧
      (∃ t < n, y t ∈ Set.range (fun z => pageMap H U (θ, z))) :=
  exists_fastPlane_open_book_aux H₀ hH₀
