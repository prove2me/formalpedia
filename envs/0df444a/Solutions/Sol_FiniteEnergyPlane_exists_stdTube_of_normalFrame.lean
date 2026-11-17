-- Prove2me | solution 1 for FiniteEnergyPlane.exists_stdTube_of_normalFrame
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-16T18:19:24.444079+00:00
-- url     : https://prove2.me/submissions/f22ec8c2-2a7d-4e96-a18b-302624b5159f

import Definitions.Def_FiniteEnergyPlane_TubeFamily
import Definitions.Def_FiniteEnergyPlane_Winding
import Theorems.Thm_FiniteEnergyPlane_asympOp_frame_bridge
import Theorems.Thm_FiniteEnergyPlane_exists_tubeModel_of_unitaryXiFrame
import Theorems.Thm_FiniteEnergyPlane_exists_ball_tubeMap_ne_zero_injective
import Theorems.Thm_FiniteEnergyPlane_fderiv_tubeMap_apply_zero
import Theorems.Thm_FiniteEnergyPlane_exists_jbar_of_tubeMap
import Theorems.Thm_FiniteEnergyPlane_expDecayCInftyTube_cylJ_sub_of_intertwining
import Theorems.Thm_FiniteEnergyPlane_exists_aCoord_proj_model_of_tubeMap



/-!
# S cf06b670: sketch glue over C1, C5, the DΦ(z,0) helper, C6a-c and the frame bridge.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem exists_stdTube_of_normalFrame_glue (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1) (hu : ContDiff ℝ ∞ u) (hu0 : ∀ z, u z ≠ 0)
    (hhol : JHolomorphic.IsJHolomorphicOn (Jtilde H J) Set.univ u) (d b : ℝ) (hb : 0 < b)
    (ha : ExpDecayCInfty (fun p : ℝ × ℝ => endA H u cylInf p - P.T * p.1 - d) b)
    (hw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H u cylInf p - P.x (P.T * p.2)) b)
    (N : ℂ → ℂ →L[ℝ] V 1) (hN : ContDiff ℝ ∞ N)
    (hNJ : ∀ (z ν : ℂ), N z (Complex.I * ν) = Jtilde H J (u z) (N z ν))
    (hNinj : ∀ (z Δ ν : ℂ), fderiv ℝ u z Δ + N z ν = 0 → Δ = 0 ∧ ν = 0)
    (M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1) (hM : IsUnitaryXiFrame J P M)
    (hNM : ∀ ν : ℂ, ExpDecayCInfty (fun p : ℝ × ℝ =>
      Real.exp (-(2 * (P.T * p.1 + d))) • N (cylInf p.1 p.2) ν - M p.2 (cToVec ν)) b) :
    ∃ ρ > 0, ∃ b' > 0, ∃ (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
      (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Sinf : ℝ → CauchyRiemannIndex.Mat 1),
      IsStdTubeStructure ρ b' Jbar Jinf Sinf ∧
      (∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j)) ∧
      (∀ η : ℝ → CauchyRiemannIndex.Vec 1, ContDiff ℝ ∞ η → Function.Periodic η 1 →
        ∀ t : ℝ, asympOp J P (fun t => M t (η t)) t =
          M t (-(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) (deriv η t)) -
            Matrix.toEuclideanLin (Sinf t) (η t))) ∧
      (∀ (z Δ ν : ℂ), fderiv ℝ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) (z, 0) (Δ, ν) =
        fderiv ℝ u z Δ + N z ν) ∧
      (∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ, u p.1 + N p.1 p.2 ≠ 0 ∧
        Function.Injective (fderiv ℝ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) p) ∧
        (fderiv ℝ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) p).comp (Jbar p) =
          (Jtilde H J (u p.1 + N p.1 p.2)).comp
            (fderiv ℝ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) p)) ∧
      (∃ (α : ℝ × ℂ → ℝ) (X : ℝ × ℂ → V 1),
        ContDiffOn ℝ ∞ α (Set.univ ×ˢ ball (0 : ℂ) ρ) ∧
        ContDiffOn ℝ ∞ X (Set.univ ×ˢ ball (0 : ℂ) ρ) ∧
        (∀ (t : ℝ) (w : ℂ), α (t + 1, w) = α (t, w) ∧ X (t + 1, w) = X (t, w)) ∧
        (∀ t : ℝ, α (t, 0) = 0 ∧ X (t, 0) = P.x (P.T * t)) ∧
        ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ =>
          aCoord H (u (cylInf q.1 q.2.1) + N (cylInf q.1 q.2.1) q.2.2) - P.T * q.1 - d -
            α (q.2.1, q.2.2)) ρ b' ∧
        ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ =>
          proj H (u (cylInf q.1 q.2.1) + N (cylInf q.1 q.2.1) q.2.2) - X (q.2.1, q.2.2)) ρ b') := by
  obtain ⟨Sinf, hSym, hSs, hA, -⟩ := (asympOp_frame_bridge H hH J hJ P).2 M hM
  obtain ⟨ρ₁, hρ₁, Jinf, hL, hJs, hJper, hJint, hSJ⟩ :=
    exists_tubeModel_of_unitaryXiFrame H hH J hJ P M hM Sinf hA
  obtain ⟨ρ₅, hρ₅, h5⟩ :=
    exists_ball_tubeMap_ne_zero_injective H hH J P u hu hu0 d b hb ha hw N hN hNinj M hM hNM
  set ρ := min ρ₁ ρ₅ with hρdef
  have hρ : 0 < ρ := lt_min hρ₁ hρ₅
  have hb1 : ball (0 : ℂ) ρ ⊆ ball 0 ρ₁ := ball_subset_ball (min_le_left _ _)
  have hb5 : ball (0 : ℂ) ρ ⊆ ball 0 ρ₅ := ball_subset_ball (min_le_right _ _)
  have hcb1 : closedBall (0 : ℂ) ρ ⊆ closedBall 0 ρ₁ := closedBall_subset_closedBall (min_le_left _ _)
  have hsub1 : (Set.univ ×ˢ ball (0 : ℂ) ρ : Set (ℝ × ℂ)) ⊆ Set.univ ×ˢ ball 0 ρ₁ :=
    Set.prod_mono subset_rfl hb1
  have hΦ : ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ, u p.1 + N p.1 p.2 ≠ 0 ∧
      Function.Injective (fderiv ℝ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) p) :=
    fun p hp => h5 p ⟨Set.mem_univ _, hb5 hp.2⟩
  have hLρ := fun t w (hw : w ∈ closedBall (0 : ℂ) ρ) => hL t w (hcb1 hw)
  obtain ⟨Jbar, hJbs, hJsq, hJ0, hJbar⟩ :=
    exists_jbar_of_tubeMap H hH J hJ u hu hhol N hN hNJ ρ hρ hΦ
  have hdec := expDecayCInftyTube_cylJ_sub_of_intertwining H hH J hJ P u hu hu0 d b hb ha hw
    N hN M hM hNM ρ hρ hLρ hΦ Jbar hJbar Jinf (fun t w hw => hJint t w (hb1 hw))
  obtain ⟨α, X, hα⟩ := exists_aCoord_proj_model_of_tubeMap H hH J P u hu0 d b hb ha hw N M hM hNM
    ρ hρ (fun t w hw => (hLρ t w hw).1) (fun p hp => (hΦ p hp).1)
  refine ⟨ρ, hρ, b, hb, Jbar, Jinf, Sinf,
    ⟨hJbs, hJsq, hJ0, hJs.mono hsub1, hJper, hdec, hSym, hSJ⟩, hSs, hA,
    fun z Δ ν => fderiv_tubeMap_apply_zero u N (hu.differentiable (by simp)) (hN.differentiable (by simp)) z Δ ν,
    fun p hp => ⟨(hΦ p hp).1, (hΦ p hp).2, hJbar p hp⟩, α, X, hα⟩

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1) (hu : ContDiff ℝ ∞ u) (hu0 : ∀ z, u z ≠ 0)
    (hhol : JHolomorphic.IsJHolomorphicOn (Jtilde H J) Set.univ u) (d b : ℝ) (hb : 0 < b)
    (ha : ExpDecayCInfty (fun p : ℝ × ℝ => endA H u cylInf p - P.T * p.1 - d) b)
    (hw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H u cylInf p - P.x (P.T * p.2)) b)
    (N : ℂ → ℂ →L[ℝ] V 1) (hN : ContDiff ℝ ∞ N)
    (hNJ : ∀ (z ν : ℂ), N z (Complex.I * ν) = Jtilde H J (u z) (N z ν))
    (hNinj : ∀ (z Δ ν : ℂ), fderiv ℝ u z Δ + N z ν = 0 → Δ = 0 ∧ ν = 0)
    (M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1) (hM : IsUnitaryXiFrame J P M)
    (hNM : ∀ ν : ℂ, ExpDecayCInfty (fun p : ℝ × ℝ =>
      Real.exp (-(2 * (P.T * p.1 + d))) • N (cylInf p.1 p.2) ν - M p.2 (cToVec ν)) b) :
    ∃ ρ > 0, ∃ b' > 0, ∃ (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
      (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Sinf : ℝ → CauchyRiemannIndex.Mat 1),
      IsStdTubeStructure ρ b' Jbar Jinf Sinf ∧
      (∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j)) ∧
      (∀ η : ℝ → CauchyRiemannIndex.Vec 1, ContDiff ℝ ∞ η → Function.Periodic η 1 →
        ∀ t : ℝ, asympOp J P (fun t => M t (η t)) t =
          M t (-(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) (deriv η t)) -
            Matrix.toEuclideanLin (Sinf t) (η t))) ∧
      (∀ (z Δ ν : ℂ), fderiv ℝ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) (z, 0) (Δ, ν) =
        fderiv ℝ u z Δ + N z ν) ∧
      (∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ, u p.1 + N p.1 p.2 ≠ 0 ∧
        Function.Injective (fderiv ℝ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) p) ∧
        (fderiv ℝ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) p).comp (Jbar p) =
          (Jtilde H J (u p.1 + N p.1 p.2)).comp
            (fderiv ℝ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) p)) ∧
      (∃ (α : ℝ × ℂ → ℝ) (X : ℝ × ℂ → V 1),
        ContDiffOn ℝ ∞ α (Set.univ ×ˢ ball (0 : ℂ) ρ) ∧
        ContDiffOn ℝ ∞ X (Set.univ ×ˢ ball (0 : ℂ) ρ) ∧
        (∀ (t : ℝ) (w : ℂ), α (t + 1, w) = α (t, w) ∧ X (t + 1, w) = X (t, w)) ∧
        (∀ t : ℝ, α (t, 0) = 0 ∧ X (t, 0) = P.x (P.T * t)) ∧
        ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ =>
          aCoord H (u (cylInf q.1 q.2.1) + N (cylInf q.1 q.2.1) q.2.2) - P.T * q.1 - d -
            α (q.2.1, q.2.2)) ρ b' ∧
        ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ =>
          proj H (u (cylInf q.1 q.2.1) + N (cylInf q.1 q.2.1) q.2.2) - X (q.2.1, q.2.2)) ρ b') :=
  exists_stdTube_of_normalFrame_glue H hH J hJ P u hu hu0 hhol d b hb ha hw N hN hNJ hNinj M hM hNM
