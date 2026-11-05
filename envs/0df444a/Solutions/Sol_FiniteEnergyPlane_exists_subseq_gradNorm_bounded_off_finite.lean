-- Prove2me | solution 1 for FiniteEnergyPlane.exists_subseq_gradNorm_bounded_off_finite
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-04T17:57:49.538961+00:00
-- url     : https://prove2.me/submissions/6415afc4-e794-45e7-acc0-0935bfa04b1d

import Definitions.Def_FiniteEnergyPlane_Compactness
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_dlambdaEnergy_univ_eq_of_isNondegenerateEnd
import Theorems.Thm_FiniteEnergyPlane_energy_univ_eq_dlambdaEnergy_of_plane
import Theorems.Thm_FiniteEnergyPlane_exists_subseq_bounded_off_finite_of_concentration
import Theorems.Thm_FiniteEnergyPlane_exists_ne_of_isNondegenerateEnd
import Theorems.Thm_FiniteEnergyPlane_exists_bubble
import Theorems.Thm_FiniteEnergyPlane_jtilde_isAlmostComplexOn



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem exists_subseq_gradNorm_bounded_off_finite_aux (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (K : Set (V 1)) (γ : ℝ) (hγ : 0 < γ)
    (hγ₁ : ∀ Q : ReebOrbit H, Q.T ≤ P.T → γ < Q.T)
    (u : ℕ → ℂ → V 1) (hu : ∀ k, u k ∈ fastPlaneSet H J P K γ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Γ : Finset ℂ, (∀ z ∈ Γ, ‖z‖ ≤ 1) ∧ (Γ.card : ℝ) * γ ≤ P.T ∧
      (∀ Kc : Set ℂ, Kc ⊆ (↑Γ)ᶜ → IsCompact Kc →
        ∃ M : ℝ, ∀ k, ∀ z ∈ Kc, gradNorm H (u (φ k)) z ≤ M) ∧
      ∀ z ∈ Γ, ∃ ζ : ℕ → ℂ, Tendsto ζ atTop (𝓝 z) ∧
        Tendsto (fun k => gradNorm H (u (φ k)) (ζ k)) atTop atTop := by
  classical
  obtain ⟨-, hprojs, haCs, -, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  have hfe : ∀ k, IsFiniteEnergyCurve H J Set.univ (u k) := fun k => (hu k).1.1
  have hnd : ∀ k, IsNondegenerateEnd H (u k) cylInf P 1 := fun k => (hu k).2.1
  have hdl : ∀ k, dlambdaEnergy H Set.univ (u k) = ENNReal.ofReal P.T := fun k =>
    dlambdaEnergy_univ_eq_of_isNondegenerateEnd H hH J hJ (u k) (hfe k) P (hnd k)
  have hE : ∀ k, energy H Set.univ (u k) ≤ ENNReal.ofReal P.T := fun k => by
    rw [energy_univ_eq_dlambdaEnergy_of_plane H hH J hJ (u k) (hfe k)
      (exists_ne_of_isNondegenerateEnd H (u k) cylInf P one_ne_zero (hnd k)), hdl k]
  set g : ℕ → ℂ → ℝ := fun k => gradNorm H (u k) with hgdef
  set f : ℕ → ℂ → ℝ≥0∞ := fun k z => ENNReal.ofReal (dlambdaDensity H (u k) z) with hfdef
  have hg : ∀ k, Continuous (g k) := by
    intro k
    obtain ⟨hsm, hne, -, -⟩ := hfe k
    have ha : ContDiff ℝ ∞ (fun z => aCoord H (u k z)) :=
      contDiffOn_univ.1 (haCs.comp hsm (fun z hz => hne z hz))
    have hp : ContDiff ℝ ∞ (fun z => proj H (u k z)) :=
      contDiffOn_univ.1 (hprojs.comp hsm (fun z hz => hne z hz))
    exact (ha.continuous_fderiv (by simp)).norm.add (hp.continuous_fderiv (by simp)).norm
  have hT : ∀ k, ∫⁻ z, f k z ≤ ENNReal.ofReal P.T := fun k => by
    have h := hdl k
    simp only [dlambdaEnergy, Measure.restrict_univ] at h
    exact h.le
  have hQ : ∀ ψ : ℕ → ℕ, StrictMono ψ → ∀ (ζ : ℕ → ℂ) (z : ℂ), Tendsto ζ atTop (𝓝 z) →
      Tendsto (fun k => g (ψ k) (ζ k)) atTop atTop →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ δ > 0, ∀ᶠ j in atTop,
        ENNReal.ofReal γ < ∫⁻ w in ball z δ, f (ψ (φ j)) w := by
    intro ψ hψ ζ z hζ hb
    obtain ⟨φ, hφ, z', r, Q, hzz, hr, hr0, -, -, hlim⟩ := exists_bubble H hH J hJ ∅
      (fun _ => Set.univ) (fun _ => isOpen_univ) (fun _ _ _ => subset_rfl)
      (fun _ _ _ => by simp) (by rw [Finset.coe_empty, Set.compl_empty]; exact Set.iUnion_const _)
      (fun k => u (ψ k)) (fun k => hfe _) P.T (fun k => hE _) ζ
      (fun _ => Set.mem_univ _) hb ⟨1, one_pos, fun _ γ hγ => by simp at hγ⟩
      (Or.inr ⟨0, 0, Set.subset_univ _⟩)
    -- the bubble's period is at most `P.T`
    have hle : limsup (fun j => dlambdaEnergy H (ball (z' j) (r j)) (u (ψ (φ j)))) atTop ≤
        ENNReal.ofReal P.T :=
      limsup_le_of_le (h := Eventually.of_forall fun j =>
        (lintegral_mono_set (Set.subset_univ _)).trans (hdl _).le)
    have hQT : Q.T ≤ P.T := by
      have h2 := hlim.trans hle
      rwa [ENNReal.ofReal_le_ofReal_iff P.T_pos.le] at h2
    have hγQ : ENNReal.ofReal γ < ENNReal.ofReal Q.T :=
      (ENNReal.ofReal_lt_ofReal_iff Q.T_pos).2 (hγ₁ Q hQT)
    have hfr : ∃ᶠ j in atTop, ENNReal.ofReal γ <
        dlambdaEnergy H (ball (z' j) (r j)) (u (ψ (φ j))) :=
      frequently_lt_of_lt_limsup (by isBoundedDefault) (lt_of_lt_of_le hγQ hlim)
    obtain ⟨θ, hθ, hθγ⟩ := extraction_of_frequently_atTop hfr
    refine ⟨φ ∘ θ, hφ.comp hθ, fun δ hδ => ?_⟩
    have hθt := hθ.tendsto_atTop
    have hφt := hφ.tendsto_atTop
    have hz'z : Tendsto z' atTop (𝓝 z) := by
      have h1 : Tendsto (fun j => ζ (φ j)) atTop (𝓝 z) := hζ.comp hφt
      rw [Metric.tendsto_atTop] at h1 ⊢
      intro ε hε
      obtain ⟨N₁, hN₁⟩ := h1 (ε / 2) (half_pos hε)
      obtain ⟨N₂, hN₂⟩ := (Metric.tendsto_atTop.1 hzz) (ε / 2) (half_pos hε)
      refine ⟨max N₁ N₂, fun j hj => ?_⟩
      have h3 := hN₁ j ((le_max_left _ _).trans hj)
      have h4 := hN₂ j ((le_max_right _ _).trans hj)
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at h4
      have h5 : dist (z' j) (ζ (φ j)) < ε / 2 := by rwa [dist_comm, dist_eq_norm]
      have := dist_triangle (z' j) (ζ (φ j)) z
      linarith
    have hsmall : ∀ᶠ j in atTop, ball (z' j) (r j) ⊆ ball z δ := by
      have e1 := (Metric.tendsto_nhds.1 hz'z) (δ / 2) (half_pos hδ)
      have e2 := (Metric.tendsto_nhds.1 hr0) (δ / 2) (half_pos hδ)
      filter_upwards [e1, e2] with j h1 h2
      refine ball_subset_ball' ?_
      rw [Real.dist_eq, sub_zero, abs_of_pos (hr j)] at h2
      linarith
    filter_upwards [hθt.eventually hsmall] with j hj
    exact lt_of_lt_of_le (hθγ j) (lintegral_mono_set hj)
  obtain ⟨φ, hφ, Γ, hcard, hbd, hpts⟩ := exists_subseq_bounded_off_finite_of_concentration g hg f
    P.T γ hγ P.T_pos.le hT hQ
  refine ⟨φ, hφ, Γ, ?_, hcard, hbd, fun z hz => (hpts z hz).1⟩
  intro z hz
  by_contra hcon
  push_neg at hcon
  obtain ⟨j, hj⟩ := ((hpts z hz).2 (‖z‖ - 1) (by linarith)).exists
  have hsub : ball z (‖z‖ - 1) ⊆ {w : ℂ | 1 < ‖w‖} := by
    intro w hw
    have h1 : dist w z < ‖z‖ - 1 := hw
    have h2 := norm_sub_norm_le z w
    rw [← dist_eq_norm, dist_comm] at h2
    simp only [Set.mem_setOf_eq]
    linarith
  have h3 : ∫⁻ w in ball z (‖z‖ - 1), f (φ j) w ≤ ENNReal.ofReal γ := by
    have h4 := (hu (φ j)).2.2.2
    refine (lintegral_mono_set hsub).trans ?_
    exact h4.le
  exact absurd hj (not_lt.2 h3)

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (K : Set (V 1)) (γ : ℝ) (hγ : 0 < γ)
    (hγ₁ : ∀ Q : ReebOrbit H, Q.T ≤ P.T → γ < Q.T)
    (u : ℕ → ℂ → V 1) (hu : ∀ k, u k ∈ fastPlaneSet H J P K γ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Γ : Finset ℂ, (∀ z ∈ Γ, ‖z‖ ≤ 1) ∧ (Γ.card : ℝ) * γ ≤ P.T ∧
      (∀ Kc : Set ℂ, Kc ⊆ (↑Γ)ᶜ → IsCompact Kc →
        ∃ M : ℝ, ∀ k, ∀ z ∈ Kc, gradNorm H (u (φ k)) z ≤ M) ∧
      ∀ z ∈ Γ, ∃ ζ : ℕ → ℂ, Tendsto ζ atTop (𝓝 z) ∧
        Tendsto (fun k => gradNorm H (u (φ k)) (ζ k)) atTop atTop :=
  exists_subseq_gradNorm_bounded_off_finite_aux H hH J hJ P K γ hγ hγ₁ u hu
