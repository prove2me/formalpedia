-- Prove2me | solution 1 for FiniteEnergyPlane.exists_norm_fderiv_qMember_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-14T12:04:47.095837+00:00
-- url     : https://prove2.me/submissions/f1a3ee91-c233-4e58-bbcb-77102646ddf4

import Definitions.Def_FiniteEnergyPlane_QMember
import Theorems.Thm_FiniteEnergyPlane_exists_norm_fderiv_qMember_le_of_norm_le_half
import Theorems.Thm_FiniteEnergyPlane_exists_norm_fderiv_qMember_le_of_half_lt_norm
import Definitions.Def_FiniteEnergyPlane_TubeFamily



-- FILE: _imports_RSK_RP4S.lean


-- FILE: QSlope.lean
/-!
# Slope weights (local helper definition, not published as a definition)

`IsSlopeWeight χ a b`: `χ` is smooth, with slope `a` on `(-∞, -1]` and slope `b` on `[1, ∞)`.
-/

namespace FiniteEnergyPlane

open scoped ContDiff

/-! ### Slope weights are affine near the ends -/

end FiniteEnergyPlane

-- FILE: RSK_RP4S.lean
namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology CauchyRiemannIndex
open scoped ContDiff Real ENNReal

noncomputable section

namespace QRB

theorem exists_norm_fderiv_qMember_le_split (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → Mat 1) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (δ δT : ℝ) (hδ : δ < 0) (hδT : δT ∈ Set.Ioo (max δ (-(2 * π))) 0)
    (χT χN β : ℝ → ℝ) (hχT : IsSlopeWeight χT π (2 * π + δT)) (hχN : IsSlopeWeight χN π δ)
    (hβ : IsLeftCutoff β) :
    ∃ ε > 0, ∃ K ≥ 0, ∀ x ∈ ball (0 : QDom) ε, qMap Jbar χT χN β x = 0 → ∀ z : ℂ,
      ‖fderiv ℝ (fun z => (qMember χT χN β x z).1) z - ContinuousLinearMap.id ℝ ℂ‖ ≤ K * ‖x‖ ∧
      (1 + ‖z‖) ^ (1 - δ / (2 * π)) * ‖fderiv ℝ (fun z => (qMember χT χN β x z).2) z‖ ≤
        K * ‖x‖ := by
  obtain ⟨ε1, h1, K1, hK1, H1⟩ := exists_norm_fderiv_qMember_le_of_norm_le_half ρ b hρ hb Jbar Jinf Sinf hstd δ δT hδ hδT χT χN β hχT hχN hβ
  obtain ⟨ε2, h2, K2, hK2, H2⟩ := exists_norm_fderiv_qMember_le_of_half_lt_norm ρ b hρ hb Jbar Jinf Sinf hstd δ δT hδ hδT χT χN β hχT hχN hβ
  refine ⟨min ε1 ε2, lt_min h1 h2, max K1 K2, le_max_of_le_left hK1, fun x hx hq z => ?_⟩
  have hx1 : x ∈ ball (0 : QDom) ε1 := ball_subset_ball (min_le_left _ _) hx
  have hx2 : x ∈ ball (0 : QDom) ε2 := ball_subset_ball (min_le_right _ _) hx
  have m1 : K1 * ‖x‖ ≤ max K1 K2 * ‖x‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  have m2 : K2 * ‖x‖ ≤ max K1 K2 * ‖x‖ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
  rcases le_or_gt ‖z‖ (1 / 2) with hz | hz
  · obtain ⟨A, B⟩ := H1 x hx1 hq z hz
    exact ⟨A.trans m1, B.trans m1⟩
  · obtain ⟨A, B⟩ := H2 x hx2 hq z hz
    exact ⟨A.trans m2, B.trans m2⟩

end QRB

end

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set CauchyRiemannIndex
open scoped ContDiff ENNReal Real

theorem solution (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → Mat 1) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (δ δT : ℝ) (hδ : δ < 0) (hδT : δT ∈ Set.Ioo (max δ (-(2 * π))) 0)
    (χT χN β : ℝ → ℝ) (hχT : IsSlopeWeight χT π (2 * π + δT)) (hχN : IsSlopeWeight χN π δ)
    (hβ : IsLeftCutoff β) :
    ∃ ε > 0, ∃ K ≥ 0, ∀ x ∈ ball (0 : QDom) ε, qMap Jbar χT χN β x = 0 → ∀ z : ℂ,
      ‖fderiv ℝ (fun z => (qMember χT χN β x z).1) z - ContinuousLinearMap.id ℝ ℂ‖ ≤ K * ‖x‖ ∧
      (1 + ‖z‖) ^ (1 - δ / (2 * π)) * ‖fderiv ℝ (fun z => (qMember χT χN β x z).2) z‖ ≤
        K * ‖x‖ :=
  QRB.exists_norm_fderiv_qMember_le_split ρ b hρ hb Jbar Jinf Sinf hstd δ δT hδ hδT χT χN β hχT hχN hβ
