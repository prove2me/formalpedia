-- Prove2me | solution 1 for FiniteEnergyPlane.infDist_endW_le_of_hasAsymptoticEigenvector
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-09T14:18:24.951227+00:00
-- url     : https://prove2.me/submissions/e86223d5-acf4-413b-9939-f1938698975c

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Theorems.Thm_FiniteEnergyPlane_exists_lipschitz_near_compact
import Theorems.Thm_FiniteEnergyPlane_contDiffAt_aCoord_proj
import Theorems.Thm_FiniteEnergyPlane_isCompact_energySurface



/-!
# Distance to the orbit along an end with an asymptotic eigenvector

`w = proj (x(τ) + h)` with `‖h‖ ≤ (sup ‖v‖ + 1) e^{εμs}`; `proj` fixes `S` and is Lipschitz on a
uniform neighbourhood of the compact `S`, so `dist(w, x(τ)) ≤ D ‖h‖`.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

lemma idp_proj_of_mem {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) {x : V n}
    (hx : x ∈ energySurface H) : proj H x = x := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    have := hH.2.2 0 hx
    simp at this
  have hx1 : H ((1 : ℝ) • x) = 1 := by rw [one_smul]; exact hx
  have hex : ∃ r : ℝ, 0 < r ∧ H (r • x) = 1 := ⟨1, one_pos, hx1⟩
  have hs : scaleToS H x = 1 := by
    unfold scaleToS
    rw [dif_pos hex]
    exact (hH.2.1 x hx0).unique (Classical.choose_spec hex) ⟨one_pos, hx1⟩
  simp [proj, hs]

lemma idp_ne_zero_of_mem {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) {x : V n}
    (hx : x ∈ energySurface H) : x ≠ 0 := by
  rintro rfl
  have := hH.2.2 0 hx
  simp at this

theorem infDist_endW_le_of_hasAsymptoticEigenvector_aux {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n) (u : ℂ → V n)
    (e : ℝ → ℝ → ℂ) (P : ReebOrbit H) (ε μ : ℝ) (v : ℝ → V n)
    (hv : HasAsymptoticEigenvector H J u e P ε μ v) :
    ∃ C s₀ : ℝ, ∀ s ≥ s₀, ∀ t : ℝ,
      infDist (endW H u e (s, t)) (Set.range P.x) ≤ C * Real.exp (ε * μ * s) := by
  obtain ⟨hev, hεμ, c, τ, r, s₀, -, hr, hform⟩ := hv
  -- `v` is bounded
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1
    (hev.1.2.1.compact_of_continuous one_ne_zero hev.1.1.continuous).isBounded
  have hMv : ∀ y, ‖v y‖ ≤ M := fun y => hM _ ⟨y, rfl⟩
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hMv 0)
  -- `r` is eventually small
  obtain ⟨s₁, hs₁⟩ := hr.2 0 1 one_pos
  have hrb : ∀ s ≥ s₁, ∀ t, ‖r (s, t)‖ ≤ 1 := fun s hs t => by
    have := hs₁ s hs t
    rwa [norm_iteratedFDeriv_zero] at this
  -- `proj` is Lipschitz near `S`
  have hO : IsOpen {y : V n | y ≠ 0} := isOpen_ne
  have hf : ContDiffOn ℝ 1 (proj H) {y : V n | y ≠ 0} := fun y hy =>
    ((contDiffAt_aCoord_proj H hH y hy).2.of_le (by exact_mod_cast le_top)).contDiffWithinAt
  obtain ⟨δ₀, hδ₀, D, hD, hK⟩ := exists_lipschitz_near_compact hO hf
    (isCompact_energySurface H hH) (fun x hx => idp_ne_zero_of_mem H hH hx)
  -- `e^{εμs}` is eventually small
  have hlim : Tendsto (fun s : ℝ => Real.exp (ε * μ * s)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg hεμ)
  obtain ⟨s₂, hs₂⟩ := eventually_atTop.1
    ((tendsto_order.1 hlim).2 (δ₀ / (M + 1)) (by positivity))
  refine ⟨D * (M + 1), max s₀ (max s₁ s₂), fun s hs t => ?_⟩
  have hs0 : s₀ ≤ s := le_trans (le_max_left _ _) hs
  have hs1 : s₁ ≤ s := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hs
  have hs2 : s₂ ≤ s := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hs
  obtain ⟨-, heq⟩ := hform s hs0 t
  set h : V n := Real.exp (ε * μ * s) • (v (τ (s, t) / P.T) + r (s, t)) with hh
  have hhn : ‖h‖ ≤ Real.exp (ε * μ * s) * (M + 1) := by
    rw [hh, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add (hMv _) (hrb s hs1 t)))
      (Real.exp_pos _).le
  have hhδ : ‖h‖ ≤ δ₀ := by
    have h2 := (hs₂ s hs2).le
    have hM1 : 0 < M + 1 := by linarith
    calc ‖h‖ ≤ Real.exp (ε * μ * s) * (M + 1) := hhn
      _ ≤ δ₀ / (M + 1) * (M + 1) := mul_le_mul_of_nonneg_right h2 hM1.le
      _ = δ₀ := div_mul_cancel₀ _ hM1.ne'
  have hxS : P.x (τ (s, t)) ∈ energySurface H := P.mem _
  obtain ⟨-, hLip⟩ := hK _ hxS
  have hy : P.x (τ (s, t)) + h ∈ closedBall (P.x (τ (s, t))) δ₀ := by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    exact hhδ
  have hLip' := (hLip _ hy).2 _ (mem_closedBall_self hδ₀.le)
  rw [idp_proj_of_mem H hH hxS, add_sub_cancel_left] at hLip'
  calc infDist (endW H u e (s, t)) (Set.range P.x)
      ≤ dist (endW H u e (s, t)) (P.x (τ (s, t))) := infDist_le_dist_of_mem ⟨_, rfl⟩
    _ = ‖proj H (P.x (τ (s, t)) + h) - P.x (τ (s, t))‖ := by rw [heq, dist_eq_norm]
    _ ≤ D * ‖h‖ := hLip'
    _ ≤ D * (Real.exp (ε * μ * s) * (M + 1)) := mul_le_mul_of_nonneg_left hhn hD
    _ = D * (M + 1) * Real.exp (ε * μ * s) := by ring

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n) (u : ℂ → V n)
    (e : ℝ → ℝ → ℂ) (P : ReebOrbit H) (ε μ : ℝ) (v : ℝ → V n)
    (hv : HasAsymptoticEigenvector H J u e P ε μ v) :
    ∃ C s₀ : ℝ, ∀ s ≥ s₀, ∀ t : ℝ,
      infDist (endW H u e (s, t)) (Set.range P.x) ≤ C * Real.exp (ε * μ * s) :=
  infDist_endW_le_of_hasAsymptoticEigenvector_aux H hH J u e P ε μ v hv
