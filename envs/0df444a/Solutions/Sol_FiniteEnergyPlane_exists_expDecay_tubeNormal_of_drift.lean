-- Prove2me | solution 1 for FiniteEnergyPlane.exists_expDecay_tubeNormal_of_drift
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-30T16:21:59.410234+00:00
-- url     : https://prove2.me/submissions/823e032a-4f03-47b7-bb59-9effc477e945

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Theorems.Thm_FiniteEnergyPlane_asympOp_frame_bridge
import Theorems.Thm_FiniteEnergyPlane_exists_crEquation_tubeNormal_of_drift
import Theorems.Thm_FiniteEnergyPlane_halfCyl_exp_decay_of_drift
import Theorems.Thm_CauchyRiemannIndex_isNondegenerate_smul_comp_affine
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Instances.Real.Lemmas



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

lemma knd_frame_bound {n : ℕ} {Z : ℝ → CauchyRiemannIndex.Vec n →L[ℝ] V n} (hc : Continuous Z)
    (hp : Function.Periodic Z 1) : ∃ B : ℝ, ∀ σ, ‖Z σ‖ ≤ B := by
  obtain ⟨B, hB⟩ := (hp.isBounded_of_continuous one_ne_zero hc).exists_norm_le
  exact ⟨B, fun σ => hB _ ⟨σ, rfl⟩⟩

lemma knd_smooth_affine {n : ℕ} (Sinf : ℝ → CauchyRiemannIndex.Mat n)
    (hSm : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j)) (ε c : ℝ) :
    ∀ i j, ContDiff ℝ ∞ (fun t => (ε • Sinf (ε * t + c)) i j) := by
  intro i j
  have ha : ContDiff ℝ ∞ (fun t : ℝ => ε * t + c) := by fun_prop
  have h : ContDiff ℝ ∞ (fun t => ε * Sinf (ε * t + c) i j) :=
    contDiff_const.mul ((hSm i j).comp ha)
  simpa [Matrix.smul_apply] using h

theorem exists_expDecay_tubeNormal_of_drift_aux {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) (P : ReebOrbit H) (hP : P.IsNondegenerate)
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (τ : ℝ × ℝ → ℝ) (h : ℝ × ℝ → V n) (s₀ : ℝ)
    (hθs : ∃ s₂ : ℝ,
      ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => τ p - ε * P.T * p.2) (Set.Ioi s₂ ×ˢ Set.univ))
    (hθ : ∀ m : ℕ, 1 ≤ m → ∀ η > 0, ∃ s₂ : ℝ, ∀ s ≥ s₂, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ m (fun p : ℝ × ℝ => τ p - ε * P.T * p.2) (s, t)‖ ≤ η)
    (hh : TendstoZeroCInfty h)
    (hrep : ∀ s ≥ s₀, ∀ t : ℝ,
      τ (s, t + 1) = τ (s, t) + ε * P.T ∧ h (s, t + 1) = h (s, t) ∧
        IsInXi H (P.x (τ (s, t))) (h (s, t)) ∧
        endW H u cylEnd (s, t) = proj H (P.x (τ (s, t)) + h (s, t))) :
    ∃ δ > 0, ∃ C s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ, ‖h (s, t)‖ ≤ C * Real.exp (-(δ * s)) := by
  have hT := P.T_pos
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have habs : |ε| = 1 := by rcases hε with rfl | rfl <;> norm_num
  obtain ⟨⟨Z, hZ⟩, hall⟩ := asympOp_frame_bridge H hH J hJ P
  obtain ⟨Sinf, hSym, hSm, hId, hiff⟩ := hall Z hZ
  obtain ⟨s₁, S, ζ, hS, hSas, hζ, hζ0, hrest⟩ :=
    exists_crEquation_tubeNormal_of_drift H hH J hJ u hu P Z hZ Sinf hSym hSm hId ε hε τ h s₀
      hθs hθ hh hrep
  obtain ⟨hSym', hnd'⟩ :=
    CauchyRiemannIndex.isNondegenerate_smul_comp_affine n Sinf hSym (hiff.1 hP) ε 0 hε
  -- the phase `φ = ε τ / T`, with `φ - t = (ε / T) θ`
  set θ : ℝ × ℝ → ℝ := fun p => τ p - ε * P.T * p.2 with hθd
  set φ : ℝ × ℝ → ℝ := fun p => ε * τ p / P.T with hφd
  have hφθ : (fun p : ℝ × ℝ => φ p - p.2) = fun p => (ε / P.T) • θ p := by
    funext p
    simp only [hφd, hθd, smul_eq_mul]
    rw [show ε * τ p / P.T - p.2 = ε / P.T * (τ p - ε * P.T * p.2) + (ε * ε - 1) * p.2 by
      field_simp; ring, hε2]
    ring
  obtain ⟨s₂, hs₂⟩ := hθs
  have hφs : ∃ s₂ : ℝ, ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => φ p - p.2) (Set.Ioi s₂ ×ˢ Set.univ) :=
    ⟨s₂, by rw [hφθ]; exact hs₂.const_smul _⟩
  have hφ : ∀ m : ℕ, 1 ≤ m → ∀ η > 0, ∃ s₃ : ℝ, ∀ s ≥ s₃, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ m (fun p : ℝ × ℝ => φ p - p.2) (s, t)‖ ≤ η := by
    intro m hm η hη
    obtain ⟨s₃, hs₃⟩ := hθ m hm (η * P.T) (by positivity)
    refine ⟨max s₃ (s₂ + 1), fun s hs t => ?_⟩
    have hU : IsOpen (Set.Ioi s₂ ×ˢ (Set.univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
    have hs2 : s₂ < s := by linarith [le_max_right s₃ (s₂ + 1)]
    have hat : ContDiffAt ℝ m θ (s, t) :=
      (hs₂.contDiffAt (hU.mem_nhds ⟨Set.mem_Ioi.2 hs2, Set.mem_univ _⟩)).of_le
        (by exact_mod_cast le_top)
    rw [hφθ, iteratedFDeriv_const_smul_apply' hat, norm_smul, Real.norm_eq_abs, abs_div, habs,
      abs_of_pos hT]
    have := hs₃ s (le_trans (le_max_left _ _) hs) t
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hT]
    linarith
  have hSas' : ∀ i j, TendstoZeroCInfty
      (fun p : ℝ × ℝ => S p i j - (fun t => ε • Sinf (ε * t + 0)) (φ p) i j) := by
    intro i j
    have e : ∀ p, ε * (ε * τ p / P.T) + 0 = τ p / P.T := fun p => by
      rw [add_zero, ← mul_div_assoc, ← mul_assoc, hε2, one_mul]
    have hfun : (fun p : ℝ × ℝ => S p i j - (fun t => ε • Sinf (ε * t + 0)) (φ p) i j) =
        fun p => S p i j - (ε • Sinf (τ p / P.T)) i j := by
      funext p
      show S p i j - (ε • Sinf (ε * (ε * τ p / P.T) + 0)) i j = _
      rw [e p]
    rw [hfun]
    exact hSas i j
  obtain ⟨δ, hδ, C, s₃, hdec⟩ :=
    halfCyl_exp_decay_of_drift s₁ S hS _ hSym' (knd_smooth_affine Sinf hSm ε 0) hnd' φ hφs hφ
      hSas' ζ hζ (fun s hs t => ⟨(hrest s hs t).1, (hrest s hs t).2.1⟩)
      (fun s hs t => (hrest s hs t).2.2.1) hζ0
  obtain ⟨B, hB⟩ := knd_frame_bound hZ.1.continuous hZ.2.1
  refine ⟨δ, hδ, max B 0 * C, max s₃ (s₁ + 1), fun s hs t => ?_⟩
  have hs₁ : s > s₁ := by linarith [le_max_right s₃ (s₁ + 1)]
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

theorem solution {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) (P : ReebOrbit H) (hP : P.IsNondegenerate)
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (τ : ℝ × ℝ → ℝ) (h : ℝ × ℝ → V n) (s₀ : ℝ)
    (hθs : ∃ s₂ : ℝ,
      ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => τ p - ε * P.T * p.2) (Set.Ioi s₂ ×ˢ Set.univ))
    (hθ : ∀ m : ℕ, 1 ≤ m → ∀ η > 0, ∃ s₂ : ℝ, ∀ s ≥ s₂, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ m (fun p : ℝ × ℝ => τ p - ε * P.T * p.2) (s, t)‖ ≤ η)
    (hh : TendstoZeroCInfty h)
    (hrep : ∀ s ≥ s₀, ∀ t : ℝ,
      τ (s, t + 1) = τ (s, t) + ε * P.T ∧ h (s, t + 1) = h (s, t) ∧
        IsInXi H (P.x (τ (s, t))) (h (s, t)) ∧
        endW H u cylEnd (s, t) = proj H (P.x (τ (s, t)) + h (s, t))) :
    ∃ δ > 0, ∃ C s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ, ‖h (s, t)‖ ≤ C * Real.exp (-(δ * s)) :=
  exists_expDecay_tubeNormal_of_drift_aux H hH J hJ u hu P hP ε hε τ h s₀ hθs hθ hh hrep
