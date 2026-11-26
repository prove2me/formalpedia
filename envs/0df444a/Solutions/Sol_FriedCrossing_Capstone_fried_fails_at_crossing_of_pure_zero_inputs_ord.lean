-- Prove2me | solution 1 for FriedCrossing.Capstone.fried_fails_at_crossing_of_pure_zero_inputs_ord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:01:55.953098+00:00
-- url     : https://prove2.me/submissions/a85be8f6-28f2-4435-9177-c945fe3bdb97

import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Theorems.Thm_FriedCrossing_PureZeros_crossing_estimates
import Theorems.Thm_FriedCrossing_PureZeros_hasDerivAt_zero_branch
import Theorems.Thm_FriedCrossing_Capstone_fried_fails_at_crossing_local_ord
import Theorems.Thm_FriedCrossing_Crossing_crossing_exists_unique_local
import Theorems.Thm_FriedCrossing_RateRatio_linearArrival_of_hasDerivAt
import Theorems.Thm_FriedCrossing_TwinRate_twin_rate_of_cluster
import Theorems.Thm_FriedCrossing_TwinRate_twin_zero


set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.Capstone
open TorsionCore OrderCount Crossing RateRatio TwinRate PureZeros
namespace FriedCrossing.Capstone
theorem _root_.solution
    -- the twin (rate file)
    (sStar : ℝ → ℝ) (a b a' b' : ℝ → ℝ → ℝ) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hderiv_a : ∀ θ τ, HasDerivAt (a θ) (a' θ τ) τ)
    (hderiv_b : ∀ θ τ, HasDerivAt (b θ) (b' θ τ) τ)
    (hcont_a : ContinuousAt (Function.uncurry a) (0, 0))
    (hcont_b : ContinuousAt (Function.uncurry b) (0, 0))
    (hcont_a' : ContinuousAt (Function.uncurry a') (0, 0))
    (hcont_b' : ContinuousAt (Function.uncurry b') (0, 0))
    (ha0 : a 0 0 = r₀) (hb0 : b 0 0 = 0)
    (hsStar0 : sStar 0 = 0) (hsStarc : ContinuousAt sStar 0)
    (hsStarneg : ∀ θ, θ ≠ 0 → sStar θ < 0)
    -- the pure degree-2 pair (this file)
    (e₁ e₂ e₁τ e₁θτ e₂τ e₂ττ e₂θττ : ℝ → ℝ → ℝ) {K₁ K₂ ε : ℝ}
    (hK₁ : 0 < K₁) (hK₂ : 0 < K₂) (hε : 0 < ε)
    (hd₁ : ∀ θ τ, HasDerivAt (e₁ θ) (e₁τ θ τ) τ)
    (hd₁' : ∀ θ τ, HasDerivAt (fun θ => e₁τ θ τ) (e₁θτ θ τ) θ)
    (hB₁ : ∀ θ τ, |θ| < ε → |τ| < ε → |e₁θτ θ τ| ≤ K₁)
    (hd₂ : ∀ θ τ, HasDerivAt (e₂ θ) (e₂τ θ τ) τ)
    (hd₂' : ∀ θ τ, HasDerivAt (e₂τ θ) (e₂ττ θ τ) τ)
    (hd₂'' : ∀ θ τ, HasDerivAt (fun θ => e₂ττ θ τ) (e₂θττ θ τ) θ)
    (hB₂ : ∀ θ τ, |θ| < ε → |τ| < ε → |e₂θττ θ τ| ≤ K₂)
    (h₁τ0 : ∀ θ, e₁ θ 0 = 0) (h₁θ0 : ∀ τ, e₁ 0 τ = 0)
    (h₂τ0 : ∀ θ, e₂ θ 0 = -(sStar θ) ^ 2) (h₂θ0 : ∀ τ, e₂ 0 τ = 0) :
    ∃ θ₀ δ : ℝ, 0 < θ₀ ∧ 0 < δ ∧ θ₀ ≤ ε ∧ δ ≤ ε ∧ ∀ θ, θ ≠ 0 → |θ| < θ₀ →
      ∀ (z R : ℝ → ℝ) (c : Fin 5 → ℕ) (τR : ℝ),
        τR ≠ 0 →
        (∀ τ, 0 ≤ disc (e₁ θ τ) (e₂ θ τ) → z τ ^ 2 - e₁ θ τ * z τ + e₂ θ τ = 0) →
        (∀ τ₀, |τ₀| < δ → twin sStar a b θ τ₀ = 0 →
          ContinuousAt z τ₀ ∧ z τ₀ = 0 ∧ e₂ θ τ₀ = 0 ∧ e₁ θ τ₀ ≠ 0) →
        (∀ τ₀, twin sStar a b θ τ₀ = 0 → ContinuousAt R τ₀) →
        (∀ τ, |τ| < δ → twin sStar a b θ τ ≠ 0 → R τ * z τ / twin sStar a b θ τ = τR) →
        (∀ τ₀, |τ₀| < δ → twin sStar a b θ τ₀ = 0 → zetaOrder c = 0) →
        ∃ σ, 0 < σ ∧ σ ≤ 2 * |sStar θ| / r₀ ∧ σ < δ ∧ twin sStar a b θ σ = 0 ∧
          (∀ τ, |τ| < δ → twin sStar a b θ τ = 0 → τ = σ) ∧
          zetaOrder c = 0 ∧
          -- the zero's slope: ∂_τe₂/e₁, steeper than the pole
          HasDerivAt z (e₂τ θ σ / e₁ θ σ) σ ∧ 2 * r₀ < |e₂τ θ σ / e₁ θ σ| ∧
          |e₁ θ σ| ≤ K₁ * |θ| * σ ∧
          ∃ α ratio : ℝ, α ≠ 0 ∧ dtwin (a θ σ) (b θ σ) (a' θ σ) (b' θ σ) σ ≠ 0 ∧
            Tendsto (fun τ => twin sStar a b θ τ / z τ) (𝓝[≠] σ) (𝓝 ratio) ∧
            ratio = dtwin (a θ σ) (b θ σ) (a' θ σ) (b' θ σ) σ / α ∧ ratio ≠ 1 ∧
            R σ = τR * ratio ∧ R σ ≠ τR ∧
            refinedTorsion 1 (dtwin (a θ σ) (b θ σ) (a' θ σ) (b' θ σ) σ /
              (α - dtwin (a θ σ) (b θ σ) (a' θ σ) (b' θ σ) σ)) =
              -(α / dtwin (a θ σ) (b θ σ) (a' θ σ) (b' θ σ) σ) := by
  obtain ⟨ε₁, hε₁, hrate⟩ := twin_rate_of_cluster sStar a b a' b' hr₀ hderiv_a hderiv_b
    hcont_a hcont_b hcont_a' hcont_b' ha0 hb0
  set δ := min ε₁ ε with hδdef
  have hδ : 0 < δ := lt_min hε₁ hε
  have hδε₁ : δ ≤ ε₁ := min_le_left _ _
  have hδε : δ ≤ ε := min_le_right _ _
  have hr2 : 0 < r₀ / 2 * δ := by positivity
  obtain ⟨θ₁, hθ₁, hsmall⟩ := Metric.continuousAt_iff.mp hsStarc (r₀ / 2 * δ) hr2
  set θ₀ := min (min ε₁ ε) (min (min (r₀ ^ 2 / (8 * K₂)) (r₀ / (16 * K₁))) θ₁) with hθ₀def
  have hθ₀ : 0 < θ₀ := by
    refine lt_min (lt_min hε₁ hε) (lt_min (lt_min ?_ ?_) hθ₁) <;> positivity
  refine ⟨θ₀, δ, hθ₀, hδ, le_trans (min_le_left _ _) (min_le_right _ _), hδε,
    fun θ hθne hθ z R c τR hτR hzQ hzc hcont hfried_off hord => ?_⟩
  -- unpack the smallness of θ
  have hθε₁ : |θ| < ε₁ := lt_of_lt_of_le hθ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hθε : |θ| < ε := lt_of_lt_of_le hθ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hθ1 : |θ| < r₀ ^ 2 / (8 * K₂) := lt_of_lt_of_le hθ
    (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hθ2 : |θ| < r₀ / (16 * K₁) := lt_of_lt_of_le hθ
    (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hθ₁' : |θ| < θ₁ := lt_of_lt_of_le hθ (le_trans (min_le_right _ _) (min_le_right _ _))
  -- the twin's rate on |τ| < δ
  have hrateδ : ∀ τ, |τ| < δ →
      HasDerivAt (twin sStar a b θ) (dtwin (a θ τ) (b θ τ) (a' θ τ) (b' θ τ) τ) τ ∧
      r₀ / 2 ≤ dtwin (a θ τ) (b θ τ) (a' θ τ) (b' θ τ) τ := fun τ hτ =>
    ⟨(hrate θ τ hθε₁ (lt_of_lt_of_le hτ hδε₁)).2.1, (hrate θ τ hθε₁ (lt_of_lt_of_le hτ hδε₁)).2.2.1⟩
  have hs0 : twin sStar a b θ 0 < 0 := by rw [twin_zero]; exact hsStarneg θ hθne
  have hsmall' : |twin sStar a b θ 0| < r₀ / 2 * δ := by
    rw [twin_zero]
    have := hsmall (by rw [Real.dist_eq, sub_zero]; exact hθ₁')
    rw [Real.dist_eq, hsStar0, sub_zero] at this
    exact this
  -- the crossing
  obtain ⟨σ, hσpos, hσle, hσlt, hσ0, huniq⟩ :=
    crossing_exists_unique_local (by positivity : (0 : ℝ) < r₀ / 2)
      (fun τ hτ => (hrateδ τ hτ).1) (fun τ hτ => (hrateδ τ hτ).2) hs0 hsmall'
  rw [twin_zero] at hσle
  have hσle' : σ ≤ 2 * |sStar θ| / r₀ := by
    calc σ ≤ |sStar θ| / (r₀ / 2) := hσle
      _ = 2 * |sStar θ| / r₀ := by rw [div_div_eq_mul_div]; ring
  have hσabs : |σ| < δ := by rw [abs_lt]; constructor <;> linarith
  -- the pure zero at the crossing
  obtain ⟨hzcont, hz0, h₂σ, h₁σ⟩ := hzc σ hσabs hσ0
  obtain ⟨hi, _, hslope⟩ := crossing_estimates sStar e₁ e₂ e₁τ e₁θτ e₂τ e₂ττ e₂θττ hr₀ hK₁ hK₂ hε
    hd₁ hd₁' hB₁ hd₂ hd₂' hd₂'' hB₂ h₁τ0 h₁θ0 h₂τ0 h₂θ0 hθε hθ1 hθ2 (hsStarneg θ hθne) hσpos
    hσle' (lt_of_lt_of_le hσlt hδε) h₂σ
  have hbig := hslope h₁σ
  have hzderiv : HasDerivAt z (e₂τ θ σ / e₁ θ σ) σ :=
    hasDerivAt_zero_branch (hd₁ θ σ) (hd₂ θ σ) h₂σ h₁σ hzQ hzcont hz0
  -- the zero's slope is not the pole's
  have hzero : ∀ τ₀, |τ₀| < δ → twin sStar a b θ τ₀ = 0 →
      ∃ α : ℝ, α ≠ 0 ∧ α ≠ dtwin (a θ τ₀) (b θ τ₀) (a' θ τ₀) (b' θ τ₀) τ₀ ∧
        LinearArrival z α τ₀ := by
    intro τ₀ hτ₀ h0
    have hτσ : τ₀ = σ := huniq τ₀ hτ₀ h0
    subst hτσ
    refine ⟨e₂τ θ τ₀ / e₁ θ τ₀, ?_, ?_, linearArrival_of_hasDerivAt hzderiv hz0⟩
    · intro h; rw [h, abs_zero] at hbig; linarith
    · intro h
      have hup := (hrate θ τ₀ hθε₁ (lt_of_lt_of_le hτ₀ hδε₁)).2.2.2
      have hlo := (hrate θ τ₀ hθε₁ (lt_of_lt_of_le hτ₀ hδε₁)).2.2.1
      rw [h, abs_of_pos (by linarith)] at hbig
      linarith
  -- assemble
  obtain ⟨σ', hσ'pos, hσ'le, hσ'lt, hσ'0, huniq', hord, α, ratio, hα, hb, hlim, hratio_eq,
      hratio, hval, hne, htors⟩ :=
    fried_fails_at_crossing_local_ord
      (twin sStar a b θ) (fun τ => dtwin (a θ τ) (b θ τ) (a' θ τ) (b' θ τ) τ) z R c
      (r₀ / 2) δ τR hτR (by positivity) hs0 hsmall' hrateδ hzero hcont hfried_off hord
  have hσσ' : σ' = σ := huniq σ' (by rw [abs_lt]; constructor <;> linarith) hσ'0
  subst hσσ'
  exact ⟨σ', hσ'pos, hσle', hσ'lt, hσ'0, huniq', hord, hzderiv, hbig, hi, α, ratio, hα, hb, hlim,
    hratio_eq, hratio, hval, hne, htors⟩
end FriedCrossing.Capstone
