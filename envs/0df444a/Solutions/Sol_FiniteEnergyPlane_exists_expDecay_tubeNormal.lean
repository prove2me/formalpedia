-- Prove2me | solution 1 for FiniteEnergyPlane.exists_expDecay_tubeNormal
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-29T21:58:18.750659+00:00
-- url     : https://prove2.me/submissions/436bc020-999a-4588-a55f-5a833ab2ffb3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Theorems.Thm_FiniteEnergyPlane_asympOp_frame_bridge
import Theorems.Thm_FiniteEnergyPlane_exists_crEquation_tubeNormal
import Theorems.Thm_FiniteEnergyPlane_halfCyl_exp_decay_eventually
import Theorems.Thm_CauchyRiemannIndex_isNondegenerate_smul_comp_affine
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Instances.Real.Lemmas



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

lemma kn_frame_bound {n : ℕ} {Z : ℝ → CauchyRiemannIndex.Vec n →L[ℝ] V n} (hc : Continuous Z)
    (hp : Function.Periodic Z 1) : ∃ B : ℝ, ∀ σ, ‖Z σ‖ ≤ B := by
  obtain ⟨B, hB⟩ := (hp.isBounded_of_continuous one_ne_zero hc).exists_norm_le
  exact ⟨B, fun σ => hB _ ⟨σ, rfl⟩⟩

lemma kn_smooth_affine {n : ℕ} (Sinf : ℝ → CauchyRiemannIndex.Mat n)
    (hSm : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j)) (ε c : ℝ) :
    ∀ i j, ContDiff ℝ ∞ (fun t => (ε • Sinf (ε * t + c)) i j) := by
  intro i j
  have ha : ContDiff ℝ ∞ (fun t : ℝ => ε * t + c) := by fun_prop
  have h : ContDiff ℝ ∞ (fun t => ε * Sinf (ε * t + c) i j) :=
    contDiff_const.mul ((hSm i j).comp ha)
  simpa [Matrix.smul_apply] using h

theorem exists_expDecay_tubeNormal_aux {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) (P : ReebOrbit H) (hP : P.IsNondegenerate)
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (c : ℝ) (τ : ℝ × ℝ → ℝ) (h : ℝ × ℝ → V n) (s₀ : ℝ)
    (hτ : TendstoZeroCInfty (fun p : ℝ × ℝ => τ p - ε * P.T * p.2 - c))
    (hh : TendstoZeroCInfty h)
    (hrep : ∀ s ≥ s₀, ∀ t : ℝ,
      τ (s, t + 1) = τ (s, t) + ε * P.T ∧ h (s, t + 1) = h (s, t) ∧
        IsInXi H (P.x (τ (s, t))) (h (s, t)) ∧
        endW H u cylEnd (s, t) = proj H (P.x (τ (s, t)) + h (s, t))) :
    ∃ δ > 0, ∃ C s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ, ‖h (s, t)‖ ≤ C * Real.exp (-(δ * s)) := by
  obtain ⟨⟨Z, hZ⟩, hall⟩ := asympOp_frame_bridge H hH J hJ P
  obtain ⟨Sinf, hSym, hSm, hId, hiff⟩ := hall Z hZ
  obtain ⟨s₁, S, ζ, hS, hSas, hζ, hζ0, hrest⟩ :=
    exists_crEquation_tubeNormal H hH J hJ u hu P Z hZ Sinf hSym hSm hId ε hε c τ h s₀ hτ hh hrep
  obtain ⟨hSym', hnd'⟩ :=
    CauchyRiemannIndex.isNondegenerate_smul_comp_affine n Sinf hSym (hiff.1 hP) ε (c / P.T) hε
  obtain ⟨δ, hδ, C, s₂, hdec⟩ :=
    halfCyl_exp_decay_eventually s₁ S hS _ hSym' (kn_smooth_affine Sinf hSm ε (c / P.T)) hSas hnd'
      ζ hζ (fun s hs t => ⟨(hrest s hs t).1, (hrest s hs t).2.1⟩)
      (fun s hs t => (hrest s hs t).2.2.1) hζ0
  obtain ⟨B, hB⟩ := kn_frame_bound hZ.1.continuous hZ.2.1
  refine ⟨δ, hδ, max B 0 * C, max s₂ (s₁ + 1), fun s hs t => ?_⟩
  have hs₁ : s > s₁ := by linarith [le_max_right s₂ (s₁ + 1)]
  rw [(hrest s hs₁ t).2.2.2]
  calc ‖Z (τ (s, t) / P.T) (ζ (s, t))‖ ≤ ‖Z (τ (s, t) / P.T)‖ * ‖ζ (s, t)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ max B 0 * (C * Real.exp (-(δ * s))) :=
        mul_le_mul ((hB _).trans (le_max_left _ _)) (hdec s ((le_max_left _ _).trans hs) t)
          (norm_nonneg _) (le_max_right _ _)
    _ = max B 0 * C * Real.exp (-(δ * s)) := by ring

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) (P : ReebOrbit H) (hP : P.IsNondegenerate)
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (c : ℝ) (τ : ℝ × ℝ → ℝ) (h : ℝ × ℝ → V n) (s₀ : ℝ)
    (hτ : TendstoZeroCInfty (fun p : ℝ × ℝ => τ p - ε * P.T * p.2 - c))
    (hh : TendstoZeroCInfty h)
    (hrep : ∀ s ≥ s₀, ∀ t : ℝ,
      τ (s, t + 1) = τ (s, t) + ε * P.T ∧ h (s, t + 1) = h (s, t) ∧
        IsInXi H (P.x (τ (s, t))) (h (s, t)) ∧
        endW H u cylEnd (s, t) = proj H (P.x (τ (s, t)) + h (s, t))) :
    ∃ δ > 0, ∃ C s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ, ‖h (s, t)‖ ≤ C * Real.exp (-(δ * s)) :=
  exists_expDecay_tubeNormal_aux H hH J hJ u hu P hP ε hε c τ h s₀ hτ hh hrep
