-- Prove2me | solution 1 for FiniteEnergyPlane.exists_jbar_family_of_window
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-12T18:22:24.6277+00:00
-- url     : https://prove2.me/submissions/ac655392-c9d9-4464-ae8d-142f195cf6c7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_FiniteEnergyPlane_Tube
import Definitions.Def_FiniteEnergyPlane_TubeFamily
import Theorems.Thm_FiniteEnergyPlane_exists_isSlopeWeight
import Theorems.Thm_FiniteEnergyPlane_exists_isLeftCutoff
import Theorems.Thm_FiniteEnergyPlane_normalCoeff_of_isStdTubeStructure
import Theorems.Thm_FiniteEnergyPlane_crApply_bijective_of_window
import Theorems.Thm_FiniteEnergyPlane_crApply_slope_bijective
import Theorems.Thm_FiniteEnergyPlane_qMap_smooth_of_isStdTubeStructure
import Theorems.Thm_FiniteEnergyPlane_exists_contDiffOn_curve_of_fderiv_surjective
import Theorems.Thm_FiniteEnergyPlane_exists_jbar_family_of_qMap_curve



/-!
# Reduction of `exists_jbar_family_of_window` to its children

The derivative at `0` of `qMap` is upper triangular with bijective diagonal blocks after adding the
constant `c`, so it is surjective and its kernel is parametrized by `c ∈ ℂ`; a curve of zeros in the
kernel direction with constant `w₀` gives the family.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology CauchyRiemannIndex
open scoped ContDiff ENNReal Real

section QLin

variable (Λ : QDom →L[ℝ] LpCyl 1 4 × LpCyl 1 4)

theorem qLin_dec (a : ↥(W1p 4 1)) (c : ℂ) (n : ↥(W1p 4 1)) :
    Λ (a, c, n) = Λ (a, 0, 0) + Λ (0, c, 0) + Λ (0, 0, n) := by
  rw [← map_add, ← map_add]
  congr 1
  simp

theorem qLin_zero : Λ ((0 : ↥(W1p 4 1)), (0 : ℂ), (0 : ↥(W1p 4 1))) = 0 := map_zero Λ

/-- An upper-triangular derivative with surjective diagonal blocks is surjective. -/
theorem qLin_surjective (hT0 : ∀ ζ : ↥(W1p 4 1), (Λ (ζ, 0, 0)).2 = 0)
    (hTs : ∀ f, ∃ ζ : ↥(W1p 4 1), (Λ (ζ, 0, 0)).1 = f)
    (hNs : ∀ f, ∃ ζ : ↥(W1p 4 1), (Λ (0, 0, ζ)).2 = f) : Function.Surjective Λ := by
  intro y
  obtain ⟨n, hn⟩ := hNs y.2
  obtain ⟨a, ha⟩ := hTs (y.1 - (Λ (0, 0, n)).1)
  refine ⟨(a, 0, n), ?_⟩
  rw [qLin_dec, qLin_zero, add_zero]
  refine Prod.ext ?_ ?_
  · simp [ha]
  · simp [hT0, hn]

/-- With injective diagonal blocks, a kernel element is determined by its constant. -/
theorem qLin_ker (hT0 : ∀ ζ : ↥(W1p 4 1), (Λ (ζ, 0, 0)).2 = 0)
    (hTi : ∀ ζ : ↥(W1p 4 1), (Λ (ζ, 0, 0)).1 = 0 → ζ = 0)
    (hNi : ∀ ζ : ↥(W1p 4 1), (Λ (0, 0, ζ)).2 = 0 → ζ = 0) :
    ∀ x : QDom, Λ x = 0 → x.2.1 = 0 → x = 0 := by
  rintro ⟨a, c, n⟩ hx hc
  simp only at hc
  subst hc
  rw [qLin_dec, qLin_zero, add_zero] at hx
  have h2 : (Λ (0, 0, n)).2 = 0 := by simpa [hT0] using congrArg Prod.snd hx
  have hn := hNi n h2
  subst hn
  rw [qLin_zero, add_zero] at hx
  have h1 : (Λ (a, 0, 0)).1 = 0 := by simpa using congrArg Prod.fst hx
  have ha := hTi a h1
  subst ha
  rfl

/-- Every constant is the constant of a kernel element. -/
theorem qLin_exists_ker (hT0 : ∀ ζ : ↥(W1p 4 1), (Λ (ζ, 0, 0)).2 = 0)
    (hTs : ∀ f, ∃ ζ : ↥(W1p 4 1), (Λ (ζ, 0, 0)).1 = f)
    (hNs : ∀ f, ∃ ζ : ↥(W1p 4 1), (Λ (0, 0, ζ)).2 = f) (w₀ : ℂ) :
    ∃ k : QDom, Λ k = 0 ∧ k.2.1 = w₀ := by
  obtain ⟨n, hn⟩ := hNs (-(Λ (0, w₀, 0)).2)
  obtain ⟨a, ha⟩ := hTs (-((Λ (0, w₀, 0)).1 + (Λ (0, 0, n)).1))
  refine ⟨(a, w₀, n), ?_, rfl⟩
  rw [qLin_dec]
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, ha, Prod.fst_zero]
    abel
  · simp [hT0, hn]

/-- The constant coordinate of `QDom`. -/
noncomputable def qConst : QDom →ₗ[ℝ] ℂ :=
  (LinearMap.fst ℝ ℂ (↥(W1p 4 1))).comp (LinearMap.snd ℝ (↥(W1p 4 1)) (ℂ × ↥(W1p 4 1)))

theorem qConst_apply (x : QDom) : qConst x = x.2.1 := rfl

end QLin

set_option maxHeartbeats 1000000 in
/-- Glue: Q from its children. -/
theorem exists_jbar_family_of_window_aux (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (δ : ℝ) (hδ : δ < 0) (hδe : ∀ e, ¬ IsLoopEigen Sinf δ e)
    (hwin : ∀ (μ : ℝ) (k : ℤ), HasLoopEigenWind Sinf μ k → (μ < δ ∧ k ≤ 0) ∨ (δ < μ ∧ 1 ≤ k))
    (l : ℕ) (hl : 1 ≤ l) (w₀ : ℂ) :
    ∃ r > 0, ∃ G : ℂ × ℝ → ℂ × ℂ, ContDiffOn ℝ l G (Set.univ ×ˢ Set.Ioo (-r) r) ∧
      (∀ z, G (z, 0) = (z, 0)) ∧ (fderiv ℝ G (0, 0) (0, 1)).2 = w₀ ∧
      (∀ t ∈ Set.Ioo (-r) r,
        ContDiff ℝ ∞ (fun z => G (z, t)) ∧ (∀ z, (G (z, t)).2 ∈ ball (0 : ℂ) ρ) ∧
        JHolomorphic.IsJHolomorphicOn Jbar Set.univ (fun z => G (z, t)) ∧
        (∃ C β : ℝ, 0 < β ∧ ∀ z, ‖(G (z, t)).1 - z‖ ≤ C * (1 + ‖z‖) ^ (1 - β)) ∧
        (∃ C : ℝ, ∀ z, ‖(G (z, t)).2‖ ≤ C * (1 + ‖z‖) ^ (δ / (2 * π))) ∧
        ∃ C : ℝ, ∀ z, ∃ Δ : ℂ, (fderiv ℝ G (z, t) (Δ, 1)).1 = 0 ∧
          ‖(fderiv ℝ G (z, t) (Δ, 1)).2‖ ≤ C * (1 + ‖z‖) ^ (δ / (2 * π))) ∧
      ∀ ε > 0, ∃ r' ∈ Set.Ioc 0 r, ∀ t ∈ Set.Ioo (-r') r', ∀ z,
        ‖(G (z, t)).1 - z‖ ≤ ε * (1 + ‖z‖) ∧ ‖(G (z, t)).2‖ ≤ ε ∧
        ‖fderiv ℝ (fun z => (G (z, t)).1) z - ContinuousLinearMap.id ℝ ℂ‖ ≤ ε ∧
        (1 + ‖z‖) * ‖fderiv ℝ (fun z => (G (z, t)).2) z‖ ≤ ε := by
  haveI : CompleteSpace ↥(W1p 4 1) := by
    unfold W1p
    exact (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have hm : max δ (-(2 * π)) < 0 := max_lt hδ (by linarith [Real.pi_pos])
  have hmle : -(2 * π) ≤ max δ (-(2 * π)) := le_max_right _ _
  set δT : ℝ := max δ (-(2 * π)) / 2 with hδTdef
  have hδT : δT ∈ Set.Ioo (max δ (-(2 * π))) 0 := ⟨by linarith, by linarith⟩
  have hbT : 2 * π + δT ∈ Set.Ioo 0 (2 * π) := ⟨by linarith [Real.pi_pos], by linarith⟩
  have hπ : π ∈ Set.Ioo 0 (2 * π) := ⟨Real.pi_pos, by linarith [Real.pi_pos]⟩
  obtain ⟨χT, hχT⟩ := exists_isSlopeWeight π (2 * π + δT)
  obtain ⟨χN, hχN⟩ := exists_isSlopeWeight π δ
  obtain ⟨β, hβ⟩ := exists_isLeftCutoff
  obtain ⟨hSs, hSper, hSinf', hSas, hA⟩ :=
    normalCoeff_of_isStdTubeStructure ρ b hρ hb Jbar Jinf Sinf hstd
  have hSinf : IsSymLoop Sinf := by
    have h' := hstd
    unfold IsStdTubeStructure at h'
    exact h'.2.2.2.2.2.2.1
  have hL := crApply_bijective_of_window 4 (by norm_num) (by norm_num) Sinf hSinf hSinf' δ hδe
    hwin (normalCoeff Jbar) hSs hSper b hb hSas hA χN hχN
  have hT := crApply_slope_bijective 4 (by norm_num) (by norm_num) π (2 * π + δT) hπ hbT χT hχT.1 hχT.2.1 hχT.2.2
  obtain ⟨εN, hεN, hF, hF0, hΛT, hΛN⟩ :=
    qMap_smooth_of_isStdTubeStructure ρ b hρ hb Jbar Jinf Sinf hstd δ δT hδ hδT χT χN β hχT hχN hβ
  obtain ⟨ε₀, hε₀, hR⟩ :=
    exists_jbar_family_of_qMap_curve ρ b hρ hb Jbar Jinf Sinf hstd δ δT hδ hδT χT χN β hχT hχN hβ l
  generalize hΛdef : fderiv ℝ (qMap Jbar χT χN β) 0 = Λ at hΛT hΛN
  have hT0 : ∀ ζ : ↥(W1p 4 1), (Λ (ζ, 0, 0)).2 = 0 := fun ζ => (hΛT ζ).2
  have hTs : ∀ f, ∃ ζ : ↥(W1p 4 1), (Λ (ζ, 0, 0)).1 = f := by
    intro f
    obtain ⟨w, hw, h⟩ := hT.2 f
    exact ⟨⟨w, hw⟩, Lp.ext (((hΛT ⟨w, hw⟩).1).trans h.symm)⟩
  have hTi : ∀ ζ : ↥(W1p 4 1), (Λ (ζ, 0, 0)).1 = 0 → ζ = 0 := by
    intro ζ h0
    apply Subtype.ext
    apply hT.1 _ ζ.2
    have h := (hΛT ζ).1
    rw [h0] at h
    exact h.symm.trans (Lp.coeFn_zero _ _ _)
  have hNs : ∀ f, ∃ ζ : ↥(W1p 4 1), (Λ (0, 0, ζ)).2 = f := by
    intro f
    obtain ⟨w, hw, h⟩ := hL.2 f
    exact ⟨⟨w, hw⟩, Lp.ext ((hΛN ⟨w, hw⟩).trans h.symm)⟩
  have hNi : ∀ ζ : ↥(W1p 4 1), (Λ (0, 0, ζ)).2 = 0 → ζ = 0 := by
    intro ζ h0
    apply Subtype.ext
    apply hL.1 _ ζ.2
    have h := hΛN ζ
    rw [h0] at h
    exact h.symm.trans (Lp.coeFn_zero _ _ _)
  have hsurj := qLin_surjective Λ hT0 hTs hNs
  have hker : ∀ x, Λ x = 0 → qConst x = 0 → x = 0 := fun x hx hc =>
    qLin_ker Λ hT0 hTi hNi x hx hc
  obtain ⟨k, hk, hkw⟩ := qLin_exists_ker Λ hT0 hTs hNs w₀
  subst hΛdef
  obtain ⟨r, hr, γ, hγ, hγ0, hγk, hγt⟩ :=
    exists_contDiffOn_curve_of_fderiv_surjective (qMap Jbar χT χN β) (min εN ε₀) (lt_min hεN hε₀)
      (hF.mono (ball_subset_ball (min_le_left _ _))) hF0 hsurj qConst hker k hk
  obtain ⟨r', hr', G, hG⟩ := hR r hr γ k hγ hγ0 hγk fun t ht =>
    ⟨ball_subset_ball (min_le_right _ _) (hγt t ht).1, (hγt t ht).2⟩
  rw [hkw] at hG
  exact ⟨r', hr', G, hG⟩

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (δ : ℝ) (hδ : δ < 0) (hδe : ∀ e, ¬ IsLoopEigen Sinf δ e)
    (hwin : ∀ (μ : ℝ) (k : ℤ), HasLoopEigenWind Sinf μ k → (μ < δ ∧ k ≤ 0) ∨ (δ < μ ∧ 1 ≤ k))
    (l : ℕ) (hl : 1 ≤ l) (w₀ : ℂ) :
    ∃ r > 0, ∃ G : ℂ × ℝ → ℂ × ℂ, ContDiffOn ℝ l G (Set.univ ×ˢ Set.Ioo (-r) r) ∧
      (∀ z, G (z, 0) = (z, 0)) ∧ (fderiv ℝ G (0, 0) (0, 1)).2 = w₀ ∧
      (∀ t ∈ Set.Ioo (-r) r,
        ContDiff ℝ ∞ (fun z => G (z, t)) ∧ (∀ z, (G (z, t)).2 ∈ ball (0 : ℂ) ρ) ∧
        JHolomorphic.IsJHolomorphicOn Jbar Set.univ (fun z => G (z, t)) ∧
        (∃ C β : ℝ, 0 < β ∧ ∀ z, ‖(G (z, t)).1 - z‖ ≤ C * (1 + ‖z‖) ^ (1 - β)) ∧
        (∃ C : ℝ, ∀ z, ‖(G (z, t)).2‖ ≤ C * (1 + ‖z‖) ^ (δ / (2 * π))) ∧
        ∃ C : ℝ, ∀ z, ∃ Δ : ℂ, (fderiv ℝ G (z, t) (Δ, 1)).1 = 0 ∧
          ‖(fderiv ℝ G (z, t) (Δ, 1)).2‖ ≤ C * (1 + ‖z‖) ^ (δ / (2 * π))) ∧
      ∀ ε > 0, ∃ r' ∈ Set.Ioc 0 r, ∀ t ∈ Set.Ioo (-r') r', ∀ z,
        ‖(G (z, t)).1 - z‖ ≤ ε * (1 + ‖z‖) ∧ ‖(G (z, t)).2‖ ≤ ε ∧
        ‖fderiv ℝ (fun z => (G (z, t)).1) z - ContinuousLinearMap.id ℝ ℂ‖ ≤ ε ∧
        (1 + ‖z‖) * ‖fderiv ℝ (fun z => (G (z, t)).2) z‖ ≤ ε :=
  exists_jbar_family_of_window_aux ρ b hρ hb Jbar Jinf Sinf hstd δ hδ hδe hwin l hl w₀
