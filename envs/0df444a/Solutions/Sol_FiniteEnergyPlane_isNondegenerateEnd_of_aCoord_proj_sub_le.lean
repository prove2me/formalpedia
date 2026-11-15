-- Prove2me | solution 1 for FiniteEnergyPlane.isNondegenerateEnd_of_aCoord_proj_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-14T18:39:22.664148+00:00
-- url     : https://prove2.me/submissions/d2bef741-81fd-46ce-9e72-5930a976f2e6

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Mathlib



/-!
# A nondegenerate end is stable under polynomially small perturbations of the coordinates
-/

namespace FiniteEnergyPlane

namespace XT

open Metric Filter Topology
open scoped ContDiff Real

lemma norm_cylInf (s t : ℝ) : ‖cylInf s t‖ = Real.exp (2 * π * s) := by
  unfold cylInf ccwLoop
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

lemma ev_exp (K c ε : ℝ) (hc : 0 < c) (hε : 0 < ε) :
    ∀ᶠ s : ℝ in atTop, K * Real.exp (-(c * s)) ≤ ε := by
  have h1 : Tendsto (fun s : ℝ => c * s) atTop atTop := tendsto_id.const_mul_atTop hc
  have h2 : Tendsto (fun s : ℝ => K * Real.exp (-(c * s))) atTop (𝓝 (K * 0)) :=
    (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul K
  rw [mul_zero] at h2
  exact h2.eventually (eventually_le_nhds hε)

lemma rpow_cyl_le (s t κ : ℝ) (hκ : 0 < κ) :
    (1 + ‖cylInf s t‖) ^ (-κ) ≤ Real.exp (-(2 * π * κ * s)) := by
  rw [norm_cylInf]
  have h1 : (1 + Real.exp (2 * π * s)) ^ (-κ) ≤ (Real.exp (2 * π * s)) ^ (-κ) :=
    Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) (by linarith) (by linarith)
  refine h1.trans (le_of_eq ?_)
  rw [← Real.exp_mul]; congr 1; ring

/-- A map whose symplectization coordinates differ from those of `u` by `O((1+‖z‖)^{-κ})` has the
same nondegenerate end. -/
lemma end_of_decay {n : ℕ} {H : V n → ℝ} {P : ReebOrbit H} {u f : ℂ → V n}
    (huP : IsNondegenerateEnd H u cylInf P 1) {R K κ : ℝ} (hκ : 0 < κ)
    (h : ∀ z, R ≤ ‖z‖ → |aCoord H (f z) - aCoord H (u z)| ≤ K * (1 + ‖z‖) ^ (-κ) ∧
      ‖proj H (f z) - proj H (u z)‖ ≤ K * (1 + ‖z‖) ^ (-κ)) :
    IsNondegenerateEnd H f cylInf P 1 := by
  obtain ⟨d, c, b, hb, hA, hW⟩ := huP
  have hπκ : 0 < π * κ := by positivity
  have hR : ∀ᶠ s : ℝ in atTop, R ≤ Real.exp (2 * π * s) := by
    have : Tendsto (fun s : ℝ => Real.exp (2 * π * s)) atTop atTop :=
      Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by positivity))
    exact this.eventually (eventually_ge_atTop R)
  have hbd : ∀ s t : ℝ, K * (1 + ‖cylInf s t‖) ^ (-κ) ≤ |K| * Real.exp (-(2 * π * κ * s)) := by
    intro s t
    calc K * (1 + ‖cylInf s t‖) ^ (-κ) ≤ |K| * (1 + ‖cylInf s t‖) ^ (-κ) :=
          mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (rpow_cyl_le s t κ hκ) (abs_nonneg K)
  refine ⟨d, c, min b (π * κ), lt_min hb hπκ, ?_, ?_⟩
  · intro ε hε
    obtain ⟨s₁, hs₁⟩ := hA (ε / 2) (by positivity)
    have ev := (eventually_ge_atTop s₁).and
      (hR.and (ev_exp |K| (2 * π * κ) (ε / 2) (by positivity) (by positivity)))
    obtain ⟨s₀, hs₀⟩ := eventually_atTop.1 ev
    refine ⟨s₀, fun s hs t => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hs₀ s hs
    have ha := hs₁ s h1 t
    have hz := (h (cylInf s t) (by rw [norm_cylInf]; exact h2)).1
    have hk := hbd s t
    dsimp only [endA] at ha ⊢
    rw [Real.norm_eq_abs] at ha ⊢
    have e : aCoord H (f (cylInf s t)) - 1 * P.T * s - d =
        (aCoord H (u (cylInf s t)) - 1 * P.T * s - d) +
          (aCoord H (f (cylInf s t)) - aCoord H (u (cylInf s t))) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    linarith
  · intro ε hε
    obtain ⟨s₁, hs₁⟩ := hW (ε / 2) (by positivity)
    have ev := (eventually_ge_atTop s₁).and ((eventually_ge_atTop (0 : ℝ)).and
      (hR.and (ev_exp |K| (π * κ) (ε / 2) hπκ (by positivity))))
    obtain ⟨s₀, hs₀⟩ := eventually_atTop.1 ev
    refine ⟨s₀, fun s hs t => ?_⟩
    obtain ⟨h1, h0, h2, h3⟩ := hs₀ s hs
    have hw := hs₁ s h1 t
    have hz := (h (cylInf s t) (by rw [norm_cylInf]; exact h2)).2
    have hk := hbd s t
    dsimp only [endW] at hw ⊢
    have e : Real.exp (min b (π * κ) * s) • (proj H (f (cylInf s t)) - P.x (1 * P.T * t + c)) =
        Real.exp (min b (π * κ) * s) • (proj H (u (cylInf s t)) - P.x (1 * P.T * t + c)) +
        Real.exp (min b (π * κ) * s) • (proj H (f (cylInf s t)) - proj H (u (cylInf s t))) := by
      rw [← smul_add]; congr 1; abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have t1 : ‖Real.exp (min b (π * κ) * s) •
        (proj H (u (cylInf s t)) - P.x (1 * P.T * t + c))‖ ≤ ε / 2 := by
      refine le_trans ?_ hw
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        abs_of_pos (Real.exp_pos _)]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply Real.exp_le_exp.2
      exact mul_le_mul_of_nonneg_right (min_le_left _ _) h0
    have t2 : ‖Real.exp (min b (π * κ) * s) •
        (proj H (f (cylInf s t)) - proj H (u (cylInf s t)))‖ ≤ ε / 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have hb' : Real.exp (min b (π * κ) * s) ≤ Real.exp (π * κ * s) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (min_le_right _ _) h0)
      calc Real.exp (min b (π * κ) * s) * ‖proj H (f (cylInf s t)) - proj H (u (cylInf s t))‖
          ≤ Real.exp (π * κ * s) * (|K| * Real.exp (-(2 * π * κ * s))) :=
            mul_le_mul hb' (hz.trans hk) (norm_nonneg _) (Real.exp_pos _).le
        _ = |K| * Real.exp (-(π * κ * s)) := by
            rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
        _ ≤ ε / 2 := h3
    linarith

end XT

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem isNondegenerateEnd_of_aCoord_proj_sub_le_aux {n : ℕ} (H : V n → ℝ) (P : ReebOrbit H)
    (u f : ℂ → V n) (huP : IsNondegenerateEnd H u cylInf P 1) (R K κ : ℝ) (hκ : 0 < κ)
    (h : ∀ z, R ≤ ‖z‖ → |aCoord H (f z) - aCoord H (u z)| ≤ K * (1 + ‖z‖) ^ (-κ) ∧
      ‖proj H (f z) - proj H (u z)‖ ≤ K * (1 + ‖z‖) ^ (-κ)) :
    IsNondegenerateEnd H f cylInf P 1 :=
  XT.end_of_decay huP hκ h

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ) (P : ReebOrbit H)
    (u f : ℂ → V n) (huP : IsNondegenerateEnd H u cylInf P 1) (R K κ : ℝ) (hκ : 0 < κ)
    (h : ∀ z, R ≤ ‖z‖ → |aCoord H (f z) - aCoord H (u z)| ≤ K * (1 + ‖z‖) ^ (-κ) ∧
      ‖proj H (f z) - proj H (u z)‖ ≤ K * (1 + ‖z‖) ^ (-κ)) :
    IsNondegenerateEnd H f cylInf P 1 :=
  isNondegenerateEnd_of_aCoord_proj_sub_le_aux H P u f huP R K κ hκ h
