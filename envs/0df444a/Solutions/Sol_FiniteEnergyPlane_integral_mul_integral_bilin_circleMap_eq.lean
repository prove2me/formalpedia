-- Prove2me | solution 1 for FiniteEnergyPlane.integral_mul_integral_bilin_circleMap_eq
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-24T23:13:56.011257+00:00
-- url     : https://prove2.me/submissions/69458ffb-7793-4555-9247-c062345055dd

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.MeasureTheory.Integral.DivergenceTheorem



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal Real Interval

set_option maxHeartbeats 1000000 in
/-- Annulus identity for a constant 2-form. -/
theorem integral_mul_integral_bilin_circleMap_eq_aux {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] (σ : F →L[ℝ] F →L[ℝ] ℝ) (hσ : ∀ x y, σ x y = -σ y x)
    {U : Set ℂ} (hU : IsOpen U) {u : ℂ → F} (hu : ContDiffOn ℝ 2 u U) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hsub : ∀ z : ℂ, a ≤ ‖z‖ → ‖z‖ ≤ b → z ∈ U) (q : F) :
    ∫ r in a..b, r * ∫ θ in 0..2 * π,
        σ (fderiv ℝ u (circleMap 0 r θ) 1) (fderiv ℝ u (circleMap 0 r θ) Complex.I) =
      (1 / 2) * (∫ θ in 0..2 * π, σ (u (circleMap 0 b θ) - q)
          (fderiv ℝ u (circleMap 0 b θ) (circleMap 0 b θ * Complex.I))) -
        (1 / 2) * (∫ θ in 0..2 * π, σ (u (circleMap 0 a θ) - q)
          (fderiv ℝ u (circleMap 0 a θ) (circleMap 0 a θ * Complex.I))) := by
  set Du := fderiv ℝ u with hDu
  set D2 := fderiv ℝ (fderiv ℝ u) with hD2
  set e : ℝ → ℂ := fun θ => circleMap 0 1 θ with he
  set P : ℝ × ℝ → ℂ := fun p => circleMap 0 p.1 p.2 with hP
  have hz : ∀ r θ : ℝ, circleMap 0 r θ = (r : ℂ) * e θ := by
    intro r θ; simp [he, circleMap]
  have hPd : Differentiable ℝ P := by
    simp only [hP]; unfold circleMap; fun_prop
  have hed : Differentiable ℝ e := by
    simp only [he]; unfold circleMap; fun_prop
  have hmemU : ∀ r θ : ℝ, r ∈ Icc a b → circleMap 0 r θ ∈ U := by
    intro r θ hr
    have hr0 : 0 < r := lt_of_lt_of_le ha hr.1
    exact hsub _ (by rw [norm_circleMap_zero, abs_of_pos hr0]; exact hr.1)
      (by rw [norm_circleMap_zero, abs_of_pos hr0]; exact hr.2)
  have hdu : ∀ z ∈ U, HasFDerivAt u (Du z) z := fun z hz =>
    ((hu.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num)).hasFDerivAt
  have hu1 : ContDiffOn ℝ 1 Du U := hu.fderiv_of_isOpen hU (by norm_num)
  have hd2 : ∀ z ∈ U, HasFDerivAt Du (D2 z) z := fun z hz =>
    ((hu1.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num)).hasFDerivAt
  have hsym : ∀ z ∈ U, ∀ v w, D2 z v w = D2 z w v := by
    intro z hz v w
    exact (hu.contDiffAt (hU.mem_nhds hz)).isSymmSndFDerivAt (by simp) v w
  -- the two components of the vector field in `(r, θ)` coordinates
  set Fr : ℝ × ℝ → ℝ := fun p => σ (u (P p) - q) (Du (P p) (P p * Complex.I)) with hFr
  set Gθ : ℝ × ℝ → ℝ := fun p => -σ (u (P p) - q) (Du (P p) (e p.2)) with hGθ
  have hFrd : ∀ p : ℝ × ℝ, p.1 ∈ Icc a b → DifferentiableAt ℝ Fr p := by
    intro p hp
    have hPU : P p ∈ U := hmemU p.1 p.2 hp
    have h1 : DifferentiableAt ℝ (fun p => u (P p) - q) p :=
      ((hdu _ hPU).differentiableAt.comp p (hPd p)).sub_const q
    have h2 : DifferentiableAt ℝ (fun p => Du (P p)) p :=
      (hd2 _ hPU).differentiableAt.comp p (hPd p)
    have h3 : DifferentiableAt ℝ (fun p => P p * Complex.I) p := (hPd p).mul_const _
    exact (σ.differentiableAt.comp p h1).clm_apply (h2.clm_apply h3)
  have hGd : ∀ p : ℝ × ℝ, p.1 ∈ Icc a b → DifferentiableAt ℝ Gθ p := by
    intro p hp
    have hPU : P p ∈ U := hmemU p.1 p.2 hp
    have h1 : DifferentiableAt ℝ (fun p => u (P p) - q) p :=
      ((hdu _ hPU).differentiableAt.comp p (hPd p)).sub_const q
    have h2 : DifferentiableAt ℝ (fun p => Du (P p)) p :=
      (hd2 _ hPU).differentiableAt.comp p (hPd p)
    have h3 : DifferentiableAt ℝ (fun p : ℝ × ℝ => e p.2) p :=
      (hed p.2).comp p differentiableAt_snd
    exact ((σ.differentiableAt.comp p h1).clm_apply (h2.clm_apply h3)).neg
  -- partial derivatives
  have hzr : ∀ r θ : ℝ, HasDerivAt (fun t : ℝ => circleMap 0 t θ) (e θ) r := by
    intro r θ
    have : HasDerivAt (fun t : ℝ => (t : ℂ) * e θ) ((1 : ℝ) * e θ) r :=
      ((hasDerivAt_id r).ofReal_comp).mul_const (e θ)
    simpa [← hz] using this
  have hr_part : ∀ r θ : ℝ, r ∈ Icc a b →
      fderiv ℝ Fr (r, θ) (1, 0) =
        σ (Du (circleMap 0 r θ) (e θ)) (Du (circleMap 0 r θ) (circleMap 0 r θ * Complex.I)) +
        σ (u (circleMap 0 r θ) - q) (D2 (circleMap 0 r θ) (e θ) (circleMap 0 r θ * Complex.I) +
          Du (circleMap 0 r θ) (e θ * Complex.I)) := by
    intro r θ hr
    set z := circleMap 0 r θ
    have hzU : z ∈ U := hmemU r θ hr
    have hline : HasDerivAt (fun t : ℝ => ((t, θ) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) r :=
      (hasDerivAt_id r).prodMk (hasDerivAt_const r θ)
    have h1 := (hFrd (r, θ) hr).hasFDerivAt.comp_hasDerivAt r hline
    have hA : HasDerivAt (fun t => u (circleMap 0 t θ) - q) (Du z (e θ)) r :=
      ((hdu z hzU).comp_hasDerivAt r (hzr r θ)).sub_const q
    have hσA := σ.hasFDerivAt.comp_hasDerivAt r hA
    have hDD : HasDerivAt (fun t => Du (circleMap 0 t θ)) (D2 z (e θ)) r :=
      (hd2 z hzU).comp_hasDerivAt r (hzr r θ)
    have hB := hDD.clm_apply ((hzr r θ).mul_const Complex.I)
    have h2 := hσA.clm_apply hB
    exact h1.unique h2
  have hθ_part : ∀ r θ : ℝ, r ∈ Icc a b →
      fderiv ℝ Gθ (r, θ) (0, 1) =
        -(σ (Du (circleMap 0 r θ) (circleMap 0 r θ * Complex.I)) (Du (circleMap 0 r θ) (e θ)) +
        σ (u (circleMap 0 r θ) - q) (D2 (circleMap 0 r θ) (circleMap 0 r θ * Complex.I) (e θ) +
          Du (circleMap 0 r θ) (e θ * Complex.I))) := by
    intro r θ hr
    set z := circleMap 0 r θ
    have hzU : z ∈ U := hmemU r θ hr
    have hline : HasDerivAt (fun t : ℝ => ((r, t) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) θ :=
      (hasDerivAt_const θ r).prodMk (hasDerivAt_id θ)
    have h1 := (hGd (r, θ) hr).hasFDerivAt.comp_hasDerivAt θ hline
    have hzθ : HasDerivAt (fun t => circleMap 0 r t) (z * Complex.I) θ := hasDerivAt_circleMap 0 r θ
    have heθ : HasDerivAt e (e θ * Complex.I) θ := hasDerivAt_circleMap 0 1 θ
    have hA : HasDerivAt (fun t => u (circleMap 0 r t) - q) (Du z (z * Complex.I)) θ :=
      ((hdu z hzU).comp_hasDerivAt θ hzθ).sub_const q
    have hσA := σ.hasFDerivAt.comp_hasDerivAt θ hA
    have hDD : HasDerivAt (fun t => Du (circleMap 0 r t)) (D2 z (z * Complex.I)) θ :=
      (hd2 z hzU).comp_hasDerivAt θ hzθ
    have hB := hDD.clm_apply heθ
    have h2 := (hσA.clm_apply hB).neg
    exact h1.unique h2
  -- the pointwise divergence
  have hlin : ∀ (L : ℂ →L[ℝ] F) (w : ℂ), ‖w‖ = 1 →
      σ (L w) (L (w * Complex.I)) = σ (L 1) (L Complex.I) := by
    intro L w hw
    have hw2 : w.re * w.re + w.im * w.im = 1 := by
      have := Complex.normSq_eq_norm_sq w
      rw [hw, Complex.normSq_apply] at this; linarith
    have e1 : w = w.re • (1 : ℂ) + w.im • Complex.I := by
      apply Complex.ext <;> simp
    have e2 : w * Complex.I = (-w.im) • (1 : ℂ) + w.re • Complex.I := by
      apply Complex.ext <;> simp
    have hXX : σ (L 1) (L 1) = 0 := by have := hσ (L 1) (L 1); linarith
    have hYY : σ (L Complex.I) (L Complex.I) = 0 := by
      have := hσ (L Complex.I) (L Complex.I); linarith
    have hYX := hσ (L Complex.I) (L 1)
    have hL1 : L w = w.re • L 1 + w.im • L Complex.I := by
      conv_lhs => rw [e1]
      rw [map_add, map_smul, map_smul]
    have hL2 : L (w * Complex.I) = (-w.im) • L 1 + w.re • L Complex.I := by
      rw [e2, map_add, map_smul, map_smul]
    rw [hL1, hL2]
    simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, hXX, hYY, hYX]
    linear_combination (σ (L 1) (L Complex.I)) * hw2
  have hdiv : ∀ r θ : ℝ, r ∈ Icc a b →
      fderiv ℝ Fr (r, θ) (1, 0) + fderiv ℝ Gθ (r, θ) (0, 1) =
        2 * (r * σ (Du (circleMap 0 r θ) 1) (Du (circleMap 0 r θ) Complex.I)) := by
    intro r θ hr
    rw [hr_part r θ hr, hθ_part r θ hr, hsym _ (hmemU r θ hr) (e θ)]
    set z := circleMap 0 r θ
    have hzI : z * Complex.I = r • (e θ * Complex.I) := by
      rw [show z = (r : ℂ) * e θ from hz r θ, Complex.real_smul]; ring
    have hen : ‖e θ‖ = 1 := by simp [he, norm_circleMap_zero]
    have key : σ (Du z (e θ)) (Du z (z * Complex.I)) = r * σ (Du z 1) (Du z Complex.I) := by
      rw [hzI, map_smul, map_smul, smul_eq_mul, hlin (Du z) (e θ) hen]
    have key2 : σ (Du z (z * Complex.I)) (Du z (e θ)) = -σ (Du z (e θ)) (Du z (z * Complex.I)) :=
      hσ _ _
    rw [key2, key]
    ring
  -- the divergence theorem on the rectangle `[a, b] × [0, 2π]`
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  have hrect : ∀ x ∈ [[a, b]] ×ˢ [[0, 2 * π]], x.1 ∈ Icc a b := by
    rintro ⟨r, θ⟩ ⟨hr, -⟩; rwa [uIcc_of_le hab] at hr
  have hDuc : ContinuousOn (fun x : ℝ × ℝ => 2 * (x.1 * σ (Du (P x) 1) (Du (P x) Complex.I)))
      ([[a, b]] ×ˢ [[0, 2 * π]]) := by
    have hc : ContinuousOn Du U := hu1.continuousOn
    have hcP : ContinuousOn (fun x : ℝ × ℝ => Du (P x)) ([[a, b]] ×ˢ [[0, 2 * π]]) :=
      hc.comp hPd.continuous.continuousOn (fun x hx => hmemU x.1 x.2 (hrect x hx))
    exact continuousOn_const.mul (continuousOn_fst.mul
      ((σ.continuous.comp_continuousOn (hcP.clm_apply continuousOn_const)).clm_apply
        (hcP.clm_apply continuousOn_const)))
  have hDiv := integral2_divergence_prod_of_hasFDerivAt Fr Gθ (fderiv ℝ Fr) (fderiv ℝ Gθ)
    a 0 b (2 * π)
    (fun x hx => (hFrd x (hrect x hx)).continuousAt.continuousWithinAt)
    (fun x hx => (hGd x (hrect x hx)).continuousAt.continuousWithinAt)
    (fun x hx => (hFrd x ⟨by rw [min_eq_left hab] at hx; exact hx.1.1.le,
      by rw [max_eq_right hab] at hx; exact hx.1.2.le⟩).hasFDerivAt)
    (fun x hx => (hGd x ⟨by rw [min_eq_left hab] at hx; exact hx.1.1.le,
      by rw [max_eq_right hab] at hx; exact hx.1.2.le⟩).hasFDerivAt)
    ((hDuc.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).congr_fun
      (fun x hx => by
        obtain ⟨r, θ⟩ := x
        exact (hdiv r θ (hrect _ hx)).symm)
      (measurableSet_uIcc.prod measurableSet_uIcc))
  -- simplify the two sides
  have hL : ∫ r in a..b, ∫ θ in (0 : ℝ)..2 * π,
      fderiv ℝ Fr (r, θ) (1, 0) + fderiv ℝ Gθ (r, θ) (0, 1) =
      2 * ∫ r in a..b, r * ∫ θ in (0 : ℝ)..2 * π,
        σ (Du (circleMap 0 r θ) 1) (Du (circleMap 0 r θ) Complex.I) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun r hr => ?_)
    rw [uIcc_of_le hab] at hr
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    rw [hdiv r θ hr]
  have hper : ∀ r : ℝ, Gθ (r, 2 * π) = Gθ (r, 0) := by
    intro r
    have h1 : circleMap 0 r (2 * π) = circleMap 0 r 0 := by
      simpa using periodic_circleMap 0 r 0
    have h2 : e (2 * π) = e 0 := by
      simpa [he] using periodic_circleMap 0 1 0
    simp only [hGθ, hP, h1, h2]
  have hR : (((∫ r in a..b, Gθ (r, 2 * π)) - ∫ r in a..b, Gθ (r, 0)) +
      ∫ θ in (0 : ℝ)..2 * π, Fr (b, θ)) - ∫ θ in (0 : ℝ)..2 * π, Fr (a, θ) =
      (∫ θ in (0 : ℝ)..2 * π, σ (u (circleMap 0 b θ) - q)
          (fderiv ℝ u (circleMap 0 b θ) (circleMap 0 b θ * Complex.I))) -
        (∫ θ in (0 : ℝ)..2 * π, σ (u (circleMap 0 a θ) - q)
          (fderiv ℝ u (circleMap 0 a θ) (circleMap 0 a θ * Complex.I))) := by
    simp only [hper, sub_self, zero_add]
    rfl
  rw [hL, hR] at hDiv
  linarith

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal Real

theorem solution {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] (σ : F →L[ℝ] F →L[ℝ] ℝ) (hσ : ∀ x y, σ x y = -σ y x)
    {U : Set ℂ} (hU : IsOpen U) {u : ℂ → F} (hu : ContDiffOn ℝ 2 u U) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hsub : ∀ z : ℂ, a ≤ ‖z‖ → ‖z‖ ≤ b → z ∈ U) (q : F) :
    ∫ r in a..b, r * ∫ θ in 0..2 * π,
        σ (fderiv ℝ u (circleMap 0 r θ) 1) (fderiv ℝ u (circleMap 0 r θ) Complex.I) =
      (1 / 2) * (∫ θ in 0..2 * π, σ (u (circleMap 0 b θ) - q)
          (fderiv ℝ u (circleMap 0 b θ) (circleMap 0 b θ * Complex.I))) -
        (1 / 2) * (∫ θ in 0..2 * π, σ (u (circleMap 0 a θ) - q)
          (fderiv ℝ u (circleMap 0 a θ) (circleMap 0 a θ * Complex.I))) :=
  integral_mul_integral_bilin_circleMap_eq_aux σ hσ hU hu ha hab hsub q
