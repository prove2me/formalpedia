-- Prove2me | solution 1 for FiniteEnergyPlane.tubeCoords_norm_le_rpow
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-16T22:01:29.404662+00:00
-- url     : https://prove2.me/submissions/b6e9cf48-b067-4ccb-be2a-bdffcf7b1305

import Definitions.Def_FiniteEnergyPlane_TubeFamily



/-!
# A3b: `C⁰` decay of the normal coordinate of a graph in a tube

If the normal coordinate is controlled by distances to the orbit (A3a), both `u` and `f` approach
the orbit at rates `(1 + |z|)^{μ/2π}` with `μ < δ` (A4), and `f = Φ(ψ, v)` with `‖Dψ - id‖ ≤ 1/2`,
then `|v z| ≤ C (1 + |z|)^{μ/2π}` for some `μ < δ`.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Linear growth from `‖Dψ - id‖ ≤ 1/2`. -/
lemma dgv_growth (ψ : ℂ → ℂ) (hψ : Differentiable ℝ ψ)
    (hDψ : ∀ z, ‖fderiv ℝ ψ z - ContinuousLinearMap.id ℝ ℂ‖ ≤ 1 / 2) (z : ℂ) :
    ‖z‖ / 2 - ‖ψ 0‖ ≤ ‖ψ z‖ := by
  set g : ℂ → ℂ := fun x => ψ x - x with hg
  have hgd : ∀ x ∈ (Set.univ : Set ℂ), DifferentiableAt ℝ g x := fun x _ =>
    (hψ x).sub differentiableAt_id
  have hgD : ∀ x ∈ (Set.univ : Set ℂ), ‖fderiv ℝ g x‖ ≤ 1 / 2 := by
    intro x _
    rw [show fderiv ℝ g x = fderiv ℝ ψ x - ContinuousLinearMap.id ℝ ℂ from
      ((hψ x).hasFDerivAt.sub (hasFDerivAt_id x)).fderiv]
    exact hDψ x
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le hgd hgD convex_univ
    (Set.mem_univ 0) (Set.mem_univ z)
  simp only [hg, sub_zero] at h
  have h2 : ‖z‖ ≤ ‖ψ z‖ + ‖ψ 0‖ + 1 / 2 * ‖z‖ := by
    have e : z = ψ z - ψ 0 - (ψ z - z - ψ 0) := by ring
    calc ‖z‖ = ‖ψ z - ψ 0 - (ψ z - z - ψ 0)‖ := by rw [← e]
      _ ≤ ‖ψ z - ψ 0‖ + ‖ψ z - z - ψ 0‖ := norm_sub_le _ _
      _ ≤ ‖ψ z‖ + ‖ψ 0‖ + 1 / 2 * ‖z‖ := by
          have := norm_sub_le (ψ z) (ψ 0)
          linarith
  linarith

theorem tubeCoords_norm_le_rpow_aux (H : V 1 → ℝ) (P : ReebOrbit H) (u : ℂ → V 1)
    (N : ℂ → ℂ →L[ℝ] V 1) (f : ℂ → V 1) (r₀ C₀ R₀ : ℝ)
    (hnorm : ∀ ζ w : ℂ, R₀ ≤ ‖ζ‖ → ‖w‖ ≤ r₀ →
      ‖w‖ ≤ C₀ * (infDist (proj H (u ζ + N ζ w)) (Set.range P.x) +
        infDist (proj H (u ζ)) (Set.range P.x)))
    (δ : ℝ) (hδ : δ < 0)
    (hδu : ∃ μ < δ, ∃ C : ℝ, ∀ z : ℂ, infDist (proj H (u z)) (Set.range P.x) ≤
      C * (1 + ‖z‖) ^ (μ / (2 * π)))
    (hδf : ∃ μ < δ, ∃ C : ℝ, ∀ z : ℂ, infDist (proj H (f z)) (Set.range P.x) ≤
      C * (1 + ‖z‖) ^ (μ / (2 * π)))
    (ψ : ℂ → ℂ) (hψ : Differentiable ℝ ψ) (v : ℂ → ℂ) (hvr : ∀ z, ‖v z‖ ≤ r₀)
    (hf : ∀ z, f z = u (ψ z) + N (ψ z) (v z))
    (hDψ : ∀ z, ‖fderiv ℝ ψ z - ContinuousLinearMap.id ℝ ℂ‖ ≤ 1 / 2) :
    ∃ μ < δ, ∃ C : ℝ, ∀ z : ℂ, ‖v z‖ ≤ C * (1 + ‖z‖) ^ (μ / (2 * π)) := by
  obtain ⟨μu, hμu, Cu, hCu⟩ := hδu
  obtain ⟨μf, hμf, Cf, hCf⟩ := hδf
  set μ : ℝ := max μu μf with hμ
  have hμδ : μ < δ := max_lt hμu hμf
  have hπ : 0 < 2 * π := by positivity
  set e : ℝ := μ / (2 * π) with he
  have he0 : e ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hπ.le
  have heu : μu / (2 * π) ≤ e := div_le_div_of_nonneg_right (le_max_left _ _) hπ.le
  have hef : μf / (2 * π) ≤ e := div_le_div_of_nonneg_right (le_max_right _ _) hπ.le
  have heu0 : μu / (2 * π) ≤ 0 := heu.trans he0
  have hr₀ : 0 ≤ r₀ := (norm_nonneg _).trans (hvr 0)
  set a : ℝ := ‖ψ 0‖
  have ha0 : 0 ≤ a := norm_nonneg _
  set R₁ : ℝ := 4 * a + 2 * |R₀| + 2 with hR₁
  have hR₁0 : 0 ≤ R₁ := by positivity
  set C₀' : ℝ := max C₀ 0
  set Cfar : ℝ := C₀' * (max Cf 0 + max Cu 0 * (4 : ℝ) ^ (-(μu / (2 * π))))
  have hRpos : 0 < (1 + R₁) ^ e := Real.rpow_pos_of_pos (by linarith) _
  set Cnear : ℝ := r₀ / (1 + R₁) ^ e
  refine ⟨μ, hμδ, max Cnear Cfar, fun z => ?_⟩
  have hp : 0 ≤ (1 + ‖z‖) ^ e := Real.rpow_nonneg (by positivity) _
  have hz1 : 1 ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
  rcases le_total ‖z‖ R₁ with hz | hz
  · -- near region
    have hmono : (1 + R₁) ^ e ≤ (1 + ‖z‖) ^ e :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) he0
    calc ‖v z‖ ≤ r₀ := hvr z
      _ = Cnear * (1 + R₁) ^ e := by rw [div_mul_cancel₀ _ hRpos.ne']
      _ ≤ Cnear * (1 + ‖z‖) ^ e := mul_le_mul_of_nonneg_left hmono (div_nonneg hr₀ hRpos.le)
      _ ≤ max Cnear Cfar * (1 + ‖z‖) ^ e := mul_le_mul_of_nonneg_right (le_max_left _ _) hp
  · -- far region
    have hg := dgv_growth ψ hψ hDψ z
    have hψR : R₀ ≤ ‖ψ z‖ := by
      have := le_abs_self R₀
      linarith
    have hψ4 : (1 + ‖z‖) / 4 ≤ 1 + ‖ψ z‖ := by
      have := abs_nonneg R₀
      linarith
    have hv := hnorm (ψ z) (v z) hψR (hvr z)
    rw [← hf z] at hv
    have h1 : infDist (proj H (f z)) (Set.range P.x) ≤ max Cf 0 * (1 + ‖z‖) ^ e := by
      refine (hCf z).trans ?_
      calc Cf * (1 + ‖z‖) ^ (μf / (2 * π)) ≤ max Cf 0 * (1 + ‖z‖) ^ (μf / (2 * π)) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by positivity) _)
        _ ≤ max Cf 0 * (1 + ‖z‖) ^ e :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hz1 hef) (le_max_right _ _)
    have h2 : infDist (proj H (u (ψ z))) (Set.range P.x) ≤
        max Cu 0 * (4 : ℝ) ^ (-(μu / (2 * π))) * (1 + ‖z‖) ^ e := by
      refine (hCu (ψ z)).trans ?_
      have hq : 0 < (1 + ‖z‖) / 4 := by positivity
      have hb1 : (1 + ‖ψ z‖) ^ (μu / (2 * π)) ≤ ((1 + ‖z‖) / 4) ^ (μu / (2 * π)) :=
        Real.rpow_le_rpow_of_nonpos hq hψ4 heu0
      have hb2 : ((1 + ‖z‖) / 4) ^ (μu / (2 * π)) =
          (4 : ℝ) ^ (-(μu / (2 * π))) * (1 + ‖z‖) ^ (μu / (2 * π)) := by
        rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (by norm_num)]
        ring
      have hb3 : (1 + ‖z‖) ^ (μu / (2 * π)) ≤ (1 + ‖z‖) ^ e :=
        Real.rpow_le_rpow_of_exponent_le hz1 heu
      have h4 : 0 ≤ (4 : ℝ) ^ (-(μu / (2 * π))) := Real.rpow_nonneg (by norm_num) _
      calc Cu * (1 + ‖ψ z‖) ^ (μu / (2 * π)) ≤ max Cu 0 * (1 + ‖ψ z‖) ^ (μu / (2 * π)) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by positivity) _)
        _ ≤ max Cu 0 * ((4 : ℝ) ^ (-(μu / (2 * π))) * (1 + ‖z‖) ^ e) := by
            refine mul_le_mul_of_nonneg_left ?_ (le_max_right _ _)
            exact hb1.trans (hb2.le.trans (mul_le_mul_of_nonneg_left hb3 h4))
        _ = max Cu 0 * (4 : ℝ) ^ (-(μu / (2 * π))) * (1 + ‖z‖) ^ e := by ring
    have hX : 0 ≤ infDist (proj H (f z)) (Set.range P.x) +
        infDist (proj H (u (ψ z))) (Set.range P.x) := add_nonneg infDist_nonneg infDist_nonneg
    calc ‖v z‖ ≤ C₀ * (infDist (proj H (f z)) (Set.range P.x) +
          infDist (proj H (u (ψ z))) (Set.range P.x)) := hv
      _ ≤ C₀' * (infDist (proj H (f z)) (Set.range P.x) +
          infDist (proj H (u (ψ z))) (Set.range P.x)) := mul_le_mul_of_nonneg_right (le_max_left _ _) hX
      _ ≤ C₀' * (max Cf 0 * (1 + ‖z‖) ^ e +
          max Cu 0 * (4 : ℝ) ^ (-(μu / (2 * π))) * (1 + ‖z‖) ^ e) :=
          mul_le_mul_of_nonneg_left (add_le_add h1 h2) (le_max_right _ _)
      _ = Cfar * (1 + ‖z‖) ^ e := by ring
      _ ≤ max Cnear Cfar * (1 + ‖z‖) ^ e := mul_le_mul_of_nonneg_right (le_max_right _ _) hp

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (P : ReebOrbit H) (u : ℂ → V 1)
    (N : ℂ → ℂ →L[ℝ] V 1) (f : ℂ → V 1) (r₀ C₀ R₀ : ℝ)
    (hnorm : ∀ ζ w : ℂ, R₀ ≤ ‖ζ‖ → ‖w‖ ≤ r₀ →
      ‖w‖ ≤ C₀ * (infDist (proj H (u ζ + N ζ w)) (Set.range P.x) +
        infDist (proj H (u ζ)) (Set.range P.x)))
    (δ : ℝ) (hδ : δ < 0)
    (hδu : ∃ μ < δ, ∃ C : ℝ, ∀ z : ℂ, infDist (proj H (u z)) (Set.range P.x) ≤
      C * (1 + ‖z‖) ^ (μ / (2 * π)))
    (hδf : ∃ μ < δ, ∃ C : ℝ, ∀ z : ℂ, infDist (proj H (f z)) (Set.range P.x) ≤
      C * (1 + ‖z‖) ^ (μ / (2 * π)))
    (ψ : ℂ → ℂ) (hψ : Differentiable ℝ ψ) (v : ℂ → ℂ) (hvr : ∀ z, ‖v z‖ ≤ r₀)
    (hf : ∀ z, f z = u (ψ z) + N (ψ z) (v z))
    (hDψ : ∀ z, ‖fderiv ℝ ψ z - ContinuousLinearMap.id ℝ ℂ‖ ≤ 1 / 2) :
    ∃ μ < δ, ∃ C : ℝ, ∀ z : ℂ, ‖v z‖ ≤ C * (1 + ‖z‖) ^ (μ / (2 * π)) :=
  tubeCoords_norm_le_rpow_aux H P u N f r₀ C₀ R₀ hnorm δ hδ hδu hδf ψ hψ v hvr hf hDψ
