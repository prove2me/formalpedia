-- Prove2me | solution 1 for FiniteEnergyPlane.exists_stdTube_of_isFastPlane
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-14T19:28:45.038491+00:00
-- url     : https://prove2.me/submissions/bef1853f-24df-4378-8ccc-9ce8fae2f4f5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_FiniteEnergyPlane_Tube
import Theorems.Thm_FiniteEnergyPlane_exists_normalFrame_of_isFastPlane
import Theorems.Thm_FiniteEnergyPlane_exists_stdTube_of_normalFrame
import Theorems.Thm_FiniteEnergyPlane_hasEigenWind_succ_of_unitaryXiFrame
import Theorems.Thm_FiniteEnergyPlane_exists_hasExpAsymptoticsEnd_of_isNondegenerateEnd
import Theorems.Thm_FiniteEnergyPlane_hasEigenWind_iff_of_shift
import Theorems.Thm_FiniteEnergyPlane_isLoopEigen_ne_zero_hasLoopEigenWind



/-!
# T `exists_stdTube_of_isFastPlane` (629359c7): glue

`Φ(z, w) = u z + N z w` for the normal frame `N` of child N; child S builds the tube structure
over the shifted orbit `P'`, and child E transfers eigen-windings through the frame `M`, which
has winding `1`. The phase `c` is undone by `hasEigenWind_iff_of_shift`.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem exists_stdTube_of_isFastPlane_glue (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1) :
    ∃ ρ > 0, ∃ b > 0, ∃ (Φ : ℂ × ℂ → V 1) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
      (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Sinf : ℝ → CauchyRiemannIndex.Mat 1),
      IsStdTubeStructure ρ b Jbar Jinf Sinf ∧ ContDiff ℝ ∞ Φ ∧ (∀ z, Φ (z, 0) = u z) ∧
      (∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ, Φ p ≠ 0 ∧ Function.Injective (fderiv ℝ Φ p) ∧
        (fderiv ℝ Φ p).comp (Jbar p) = (Jtilde H J (Φ p)).comp (fderiv ℝ Φ p)) ∧
      (∃ τ : ℂ, fderiv ℝ Φ (0, 0) (τ, 1) = u 0) ∧
      (∃ (d c : ℝ) (α : ℝ × ℂ → ℝ) (X : ℝ × ℂ → V 1),
        ContDiffOn ℝ ∞ α (Set.univ ×ˢ ball (0 : ℂ) ρ) ∧
        ContDiffOn ℝ ∞ X (Set.univ ×ˢ ball (0 : ℂ) ρ) ∧
        (∀ (t : ℝ) (w : ℂ), α (t + 1, w) = α (t, w) ∧ X (t + 1, w) = X (t, w)) ∧
        (∀ t : ℝ, α (t, 0) = 0 ∧ X (t, 0) = P.x (P.T * t + c)) ∧
        ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ =>
          aCoord H (Φ (cylInf q.1 q.2.1, q.2.2)) - P.T * q.1 - d - α (q.2.1, q.2.2)) ρ b ∧
        ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ =>
          proj H (Φ (cylInf q.1 q.2.1, q.2.2)) - X (q.2.1, q.2.2)) ρ b) ∧
      (∀ (μ : ℝ) e, IsLoopEigen Sinf μ e → ∃ v, IsAsymptoticEigen J P μ v) ∧
      (∀ (μ : ℝ) (k : ℤ), HasLoopEigenWind Sinf μ k → HasEigenWind J P μ (k + 1)) := by
  obtain ⟨hfe, -, -⟩ := id hu
  obtain ⟨d, c, b, P', N, M, hb, hT, hx, ha, hw, hN, hNJ, hNinj, ⟨τ, hτ⟩, hM, hwind, hNM⟩ :=
    exists_normalFrame_of_isFastPlane H hH J hJ P u hu huP
  have huC : ContDiff ℝ ∞ u := contDiffOn_univ.1 hfe.1
  have hu0 : ∀ z, u z ≠ 0 := fun z => hfe.2.1 z (Set.mem_univ _)
  rw [← hT] at ha hw hNM
  obtain ⟨ρ, hρ, b', hb', Jbar, Jinf, Sinf, hstd, hS', hA, hD0, htube, α, X, hα, hX, hper, h0,
      hda, hdX⟩ :=
    exists_stdTube_of_normalFrame H hH J hJ P' u huC hu0 hfe.2.2.1 d b hb ha hw N hN hNJ hNinj M
      hM hNM
  have hE : ∀ (μ : ℝ) (k : ℤ), HasLoopEigenWind Sinf μ k → HasEigenWind J P μ (k + 1) :=
    fun μ k h => (hasEigenWind_iff_of_shift J P P' c hT hx μ (k + 1)).2
      (hasEigenWind_succ_of_unitaryXiFrame J P' M hM hwind Sinf hstd.2.2.2.2.2.2.1 hS' hA μ k h)
  refine ⟨ρ, hρ, b', hb', fun q => u q.1 + N q.1 q.2, Jbar, Jinf, Sinf, hstd, ?_, ?_, htube,
    ⟨τ, by rw [hD0]; exact hτ⟩, ⟨d, c, α, X, hα, hX, hper, ?_, ?_, hdX⟩, ?_, hE⟩
  · exact (huC.comp contDiff_fst).add ((hN.comp contDiff_fst).clm_apply contDiff_snd)
  · intro z
    simp
  · intro t
    refine ⟨(h0 t).1, ?_⟩
    rw [(h0 t).2, hx, hT]
  · simpa only [hT] using hda
  · intro μ e he
    obtain ⟨-, k, hk⟩ :=
      isLoopEigen_ne_zero_hasLoopEigenWind Sinf hstd.2.2.2.2.2.2.1 hS' μ e he
    exact (hE μ k hk).1

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1) :
    ∃ ρ > 0, ∃ b > 0, ∃ (Φ : ℂ × ℂ → V 1) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
      (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Sinf : ℝ → CauchyRiemannIndex.Mat 1),
      IsStdTubeStructure ρ b Jbar Jinf Sinf ∧ ContDiff ℝ ∞ Φ ∧ (∀ z, Φ (z, 0) = u z) ∧
      (∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ, Φ p ≠ 0 ∧ Function.Injective (fderiv ℝ Φ p) ∧
        (fderiv ℝ Φ p).comp (Jbar p) = (Jtilde H J (Φ p)).comp (fderiv ℝ Φ p)) ∧
      (∃ τ : ℂ, fderiv ℝ Φ (0, 0) (τ, 1) = u 0) ∧
      (∃ (d c : ℝ) (α : ℝ × ℂ → ℝ) (X : ℝ × ℂ → V 1),
        ContDiffOn ℝ ∞ α (Set.univ ×ˢ ball (0 : ℂ) ρ) ∧
        ContDiffOn ℝ ∞ X (Set.univ ×ˢ ball (0 : ℂ) ρ) ∧
        (∀ (t : ℝ) (w : ℂ), α (t + 1, w) = α (t, w) ∧ X (t + 1, w) = X (t, w)) ∧
        (∀ t : ℝ, α (t, 0) = 0 ∧ X (t, 0) = P.x (P.T * t + c)) ∧
        ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ =>
          aCoord H (Φ (cylInf q.1 q.2.1, q.2.2)) - P.T * q.1 - d - α (q.2.1, q.2.2)) ρ b ∧
        ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ =>
          proj H (Φ (cylInf q.1 q.2.1, q.2.2)) - X (q.2.1, q.2.2)) ρ b) ∧
      (∀ (μ : ℝ) e, IsLoopEigen Sinf μ e → ∃ v, IsAsymptoticEigen J P μ v) ∧
      (∀ (μ : ℝ) (k : ℤ), HasLoopEigenWind Sinf μ k → HasEigenWind J P μ (k + 1)) :=
  exists_stdTube_of_isFastPlane_glue H hH J hJ P u hu huP
