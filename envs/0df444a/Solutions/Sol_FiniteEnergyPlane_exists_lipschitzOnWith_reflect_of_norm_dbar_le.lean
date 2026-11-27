-- Prove2me | solution 1 for FiniteEnergyPlane.exists_lipschitzOnWith_reflect_of_norm_dbar_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-27T00:29:26.292751+00:00
-- url     : https://prove2.me/submissions/006425a0-d0eb-4ed6-8a95-ace546eff1e4

import Definitions.Def_FiniteEnergyPlane_Setting
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.MeanValue

open Metric MeasureTheory
open scoped NNReal
open Metric MeasureTheory Set Filter Topology

namespace FiniteEnergyPlane

theorem c2br_norm_inv_conj_sub_le {z w : ℂ} (hz : 1 ≤ ‖z‖) (hw : 1 ≤ ‖w‖) :
    ‖(starRingEnd ℂ z)⁻¹ - (starRingEnd ℂ w)⁻¹‖ ≤ ‖z - w‖ := by
  have hz0 : z ≠ 0 := by rintro rfl; norm_num at hz
  have hw0 : w ≠ 0 := by rintro rfl; norm_num at hw
  have hcz : starRingEnd ℂ z ≠ 0 := by simpa using hz0
  have hcw : starRingEnd ℂ w ≠ 0 := by simpa using hw0
  have key : (starRingEnd ℂ z)⁻¹ - (starRingEnd ℂ w)⁻¹ =
      (starRingEnd ℂ w - starRingEnd ℂ z) / (starRingEnd ℂ z * starRingEnd ℂ w) := by
    field_simp
  rw [key, norm_div, norm_mul, Complex.norm_conj, Complex.norm_conj, ← map_sub,
    Complex.norm_conj, norm_sub_rev]
  have h1 : 1 ≤ ‖z‖ * ‖w‖ := by nlinarith
  exact div_le_self (norm_nonneg _) h1

theorem c2br_inv_conj_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) : (starRingEnd ℂ z)⁻¹ = z := by
  have : z * starRingEnd ℂ z = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]; norm_num
  exact inv_eq_of_mul_eq_one_left this

theorem c2br_dbar_identity (a b c : ℂ) :
    starRingEnd ℂ ((c.re : ℂ) * a + (c.im : ℂ) * b) +
        Complex.I * starRingEnd ℂ ((c.im : ℂ) * a + ((-c.re : ℝ) : ℂ) * b) =
      c * starRingEnd ℂ (a + Complex.I * b) := by
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  conv_rhs => rw [← Complex.re_add_im c]
  push_cast
  linear_combination ((c.im : ℂ) * starRingEnd ℂ b) * Complex.I_sq

theorem c2br_clm_apply (D : ℂ →L[ℝ] ℂ) (c : ℂ) :
    D c = (c.re : ℂ) * D 1 + (c.im : ℂ) * D Complex.I := by
  have : c = c.re • (1 : ℂ) + c.im • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [this]
  rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]

/-- Reflection across the unit circle near a boundary point. -/
theorem exists_lipschitzOnWith_reflect_aux (g : ℂ → ℂ) (z₁ : ℂ)
    (hz₁ : z₁ ∈ sphere (0 : ℂ) 1) (r : ℝ) (hr : 0 < r)
    (hg : ContDiffOn ℝ 1 g (closedBall 0 1 ∩ ball z₁ r)) (M : ℝ)
    (hM : ∀ z ∈ ball (0 : ℂ) 1 ∩ ball z₁ r,
      ‖fderiv ℝ g z 1 + Complex.I * fderiv ℝ g z Complex.I‖ ≤ M * ‖g z‖)
    (hreal : ∀ z ∈ sphere (0 : ℂ) 1 ∩ ball z₁ r, (g z).im = 0) :
    ∃ ρ > (0 : ℝ), ∃ K : ℝ≥0, ∃ M' : ℝ,
      LipschitzOnWith K
        (fun z => if ‖z‖ ≤ 1 then g z else starRingEnd ℂ (g (starRingEnd ℂ z)⁻¹)) (ball z₁ ρ) ∧
      ∀ᵐ z ∂(volume.restrict (ball z₁ ρ)),
        ‖fderiv ℝ (fun z => if ‖z‖ ≤ 1 then g z else starRingEnd ℂ (g (starRingEnd ℂ z)⁻¹)) z 1 +
            Complex.I * fderiv ℝ
              (fun z => if ‖z‖ ≤ 1 then g z else starRingEnd ℂ (g (starRingEnd ℂ z)⁻¹)) z
              Complex.I‖ ≤
          M' * ‖(fun z => if ‖z‖ ≤ 1 then g z else starRingEnd ℂ (g (starRingEnd ℂ z)⁻¹)) z‖ := by
  set G : ℂ → ℂ := fun z => if ‖z‖ ≤ 1 then g z else starRingEnd ℂ (g (starRingEnd ℂ z)⁻¹)
    with hGdef
  have hz₁n : ‖z₁‖ = 1 := by simpa using hz₁
  set ρ : ℝ := min (r / 2) (1 / 2) with hρdef
  have hρ0 : 0 < ρ := by positivity
  have hρr : ρ < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hρh : ρ ≤ 1 / 2 := min_le_right _ _
  set D : Set ℂ := closedBall (0 : ℂ) 1 ∩ ball z₁ r with hDdef
  set S : Set ℂ := closedBall (0 : ℂ) 1 ∩ closedBall z₁ ρ with hSdef
  have hSD : S ⊆ D := fun z hz =>
    ⟨hz.1, lt_of_le_of_lt (mem_closedBall.1 hz.2) hρr⟩
  have hSc : IsCompact S := (isCompact_closedBall _ _).inter_right isClosed_closedBall
  have hSconv : Convex ℝ S := (convex_closedBall _ _).inter (convex_closedBall _ _)
  have hDconv : Convex ℝ D := (convex_closedBall _ _).inter (convex_ball _ _)
  -- an interior point of `D`
  have hpt : ((1 - ρ : ℝ) : ℂ) * z₁ ∈ ball (0 : ℂ) 1 ∩ ball z₁ r := by
    refine ⟨?_, ?_⟩
    · rw [mem_ball_zero_iff, norm_mul, hz₁n, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith)]
      linarith
    · have : ((1 - ρ : ℝ) : ℂ) * z₁ - z₁ = ((-ρ : ℝ) : ℂ) * z₁ := by push_cast; ring
      rw [mem_ball, dist_eq_norm, this, norm_mul, hz₁n, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_neg, abs_of_pos hρ0]
      exact hρr
  have hintD : ball (0 : ℂ) 1 ∩ ball z₁ r ⊆ D := inter_subset_inter_left _ ball_subset_closedBall
  have hDint : (interior D).Nonempty :=
    ⟨_, interior_maximal hintD (isOpen_ball.inter isOpen_ball) hpt⟩
  have hU : UniqueDiffOn ℝ D := uniqueDiffOn_convex hDconv hDint
  have hfc : ContinuousOn (fderivWithin ℝ g D) D := hg.continuousOn_fderivWithin hU le_rfl
  obtain ⟨C, hC⟩ := hSc.exists_bound_of_continuousOn (hfc.mono hSD)
  set K : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩ with hKdef
  have hlipS : LipschitzOnWith K g S := by
    refine Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le (f' := fderivWithin ℝ g D)
      (fun x hx => ?_) (fun x hx => ?_) hSconv
    · exact ((hg.differentiableOn one_ne_zero x (hSD hx)).hasFDerivWithinAt).mono hSD
    · rw [← NNReal.coe_le_coe, coe_nnnorm]
      exact (hC x hx).trans (le_max_left _ _)
  -- geometry of the reflection
  have hball_norm : ∀ z ∈ ball z₁ ρ, 1 / 2 ≤ ‖z‖ := by
    intro z hz
    have h1 := norm_sub_norm_le z₁ z
    rw [mem_ball, dist_eq_norm] at hz
    rw [norm_sub_rev] at hz
    linarith
  have hσS : ∀ z ∈ ball z₁ ρ, 1 ≤ ‖z‖ → (starRingEnd ℂ z)⁻¹ ∈ S := by
    intro z hz hz1
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall, dist_zero_right, norm_inv, Complex.norm_conj]
      exact inv_le_one_of_one_le₀ hz1
    · rw [mem_closedBall, dist_eq_norm]
      have := c2br_norm_inv_conj_sub_le hz1 hz₁n.ge
      rw [c2br_inv_conj_of_norm_eq_one hz₁n] at this
      exact this.trans (by rw [← dist_eq_norm]; exact (mem_ball.1 hz).le)
  have hGin : ∀ z, ‖z‖ ≤ 1 → G z = g z := fun z hz => by simp only [hGdef, if_pos hz]
  have hGout : ∀ z ∈ ball z₁ ρ, 1 ≤ ‖z‖ → G z = starRingEnd ℂ (g (starRingEnd ℂ z)⁻¹) := by
    intro z hz hz1
    by_cases h : ‖z‖ ≤ 1
    · have hz1' : ‖z‖ = 1 := le_antisymm h hz1
      rw [hGin z h, c2br_inv_conj_of_norm_eq_one hz1']
      have hre := hreal z ⟨by simpa using hz1', lt_of_lt_of_le (mem_ball.1 hz) hρr.le⟩
      apply Complex.ext <;> simp [hre]
    · simp only [hGdef, if_neg h]
  have hsame : ∀ z ∈ ball z₁ ρ, ∀ w ∈ ball z₁ ρ,
      (‖z‖ ≤ 1 ∧ ‖w‖ ≤ 1) ∨ (1 ≤ ‖z‖ ∧ 1 ≤ ‖w‖) → dist (G z) (G w) ≤ K * dist z w := by
    intro z hz w hw h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [hGin z h1, hGin w h2]
      exact hlipS.dist_le_mul z ⟨by simpa using h1, (mem_ball.1 hz).le⟩ w
        ⟨by simpa using h2, (mem_ball.1 hw).le⟩
    · rw [hGout z hz h1, hGout w hw h2, Complex.dist_conj_conj]
      refine (hlipS.dist_le_mul _ (hσS z hz h1) _ (hσS w hw h2)).trans ?_
      gcongr
      rw [dist_eq_norm, dist_eq_norm]
      exact c2br_norm_inv_conj_sub_le h1 h2
  have hmix : ∀ z ∈ ball z₁ ρ, ∀ w ∈ ball z₁ ρ, ‖z‖ ≤ 1 → 1 ≤ ‖w‖ →
      dist (G z) (G w) ≤ K * dist z w := by
    intro z hz w hw h1 h2
    have hcont : ContinuousOn (fun t : ℝ => ‖z + t • (w - z)‖) (Icc 0 1) := by
      fun_prop
    obtain ⟨t, ht, hct⟩ := intermediate_value_Icc zero_le_one hcont
      ⟨by simpa using h1, by simpa using h2⟩
    set c := z + t • (w - z) with hcdef
    have hc : c ∈ ball z₁ ρ := (convex_ball z₁ ρ).add_smul_sub_mem hz hw ht
    have hcn : ‖c‖ = 1 := hct
    have hzc : dist z c = t * dist z w := by
      rw [hcdef, dist_eq_norm, dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg ht.1, norm_sub_rev]
    have hcw : dist c w = (1 - t) * dist z w := by
      have : z + t • (w - z) - w = (1 - t) • (z - w) := by
        rw [sub_smul, one_smul, smul_sub, smul_sub]; abel
      rw [hcdef, dist_eq_norm, dist_eq_norm, this, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by linarith [ht.2])]
    calc dist (G z) (G w) ≤ dist (G z) (G c) + dist (G c) (G w) := dist_triangle _ _ _
      _ ≤ K * dist z c + K * dist c w := by
          gcongr
          · exact hsame z hz c hc (Or.inl ⟨h1, hcn.le⟩)
          · exact hsame c hc w hw (Or.inr ⟨hcn.ge, h2⟩)
      _ = K * dist z w := by rw [hzc, hcw]; ring
  refine ⟨ρ, hρ0, K, |M|, ?_, ?_⟩
  · refine LipschitzOnWith.of_dist_le_mul fun z hz w hw => ?_
    by_cases h1 : ‖z‖ ≤ 1
    · by_cases h2 : ‖w‖ ≤ 1
      · exact hsame z hz w hw (Or.inl ⟨h1, h2⟩)
      · exact hmix z hz w hw h1 (le_of_lt (not_le.1 h2))
    · by_cases h2 : ‖w‖ ≤ 1
      · rw [dist_comm, dist_comm z]
        exact hmix w hw z hz h2 (le_of_lt (not_le.1 h1))
      · exact hsame z hz w hw (Or.inr ⟨(not_le.1 h1).le, (not_le.1 h2).le⟩)
  · -- off the unit circle (a null set) the bound holds pointwise
    have hnull : ∀ᵐ z ∂(volume : Measure ℂ), z ∉ sphere (0 : ℂ) 1 :=
      (measure_eq_zero_iff_ae_notMem).1 (Measure.addHaar_sphere volume 0 1)
    rw [ae_restrict_iff' measurableSet_ball]
    filter_upwards [hnull] with z hzs hz
    have hzs' : ‖z‖ ≠ 1 := by simpa using hzs
    rcases lt_or_gt_of_ne hzs' with hlt | hgt
    · -- inside the disc
      have hev : G =ᶠ[𝓝 z] g := by
        filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hlt] with y hy
        exact hGin y (le_of_lt hy)
      rw [hev.fderiv_eq, hGin z hlt.le]
      refine (hM z ⟨mem_ball_zero_iff.2 hlt, lt_of_lt_of_le (mem_ball.1 hz) hρr.le⟩).trans ?_
      exact mul_le_mul_of_nonneg_right (le_abs_self M) (norm_nonneg _)
    · -- outside the disc
      set F : ℂ → ℂ := fun y => starRingEnd ℂ (g (starRingEnd ℂ y)⁻¹) with hFdef
      have hev : G =ᶠ[𝓝 z] F := by
        filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hgt] with y hy
        simp only [hGdef, hFdef, if_neg (not_le.2 hy)]
      have hz0 : z ≠ 0 := by rintro rfl; norm_num at hgt
      have hcz : starRingEnd ℂ z ≠ 0 := by simpa using hz0
      set w : ℂ := (starRingEnd ℂ z)⁻¹ with hwdef
      have hwS : w ∈ ball (0 : ℂ) 1 ∩ ball z₁ r := by
        refine ⟨?_, ?_⟩
        · rw [mem_ball_zero_iff, hwdef, norm_inv, Complex.norm_conj]
          exact inv_lt_one_of_one_lt₀ hgt
        · exact lt_of_le_of_lt (mem_closedBall.1 (hσS z hz hgt.le).2) hρr
      have hgw : HasFDerivAt g (fderiv ℝ g w) w := by
        have hmem : D ∈ 𝓝 w :=
          Filter.mem_of_superset ((isOpen_ball.inter isOpen_ball).mem_nhds hwS) hintD
        exact ((hg.contDiffAt hmem).differentiableAt one_ne_zero).hasFDerivAt
      have hconj : HasFDerivAt (fun y : ℂ => starRingEnd ℂ y)
          (Complex.conjCLE : ℂ →L[ℝ] ℂ) z := Complex.conjCLE.hasFDerivAt
      have hinv : HasFDerivAt (fun y : ℂ => y⁻¹)
          ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
            (-((starRingEnd ℂ z) ^ 2)⁻¹)).restrictScalars ℝ) (starRingEnd ℂ z) :=
        (hasDerivAt_inv hcz).hasFDerivAt.restrictScalars ℝ
      have hσd := hinv.comp z hconj
      have hgσ := hgw.comp z hσd
      have hF := (Complex.conjCLE.hasFDerivAt (x := g w)).comp z hgσ
      have hFF : HasFDerivAt F _ z := hF
      rw [hev.fderiv_eq, hFF.fderiv]
      set c : ℂ := -((starRingEnd ℂ z) ^ 2)⁻¹ with hcdef
      set Dg := fderiv ℝ g w with hDgdef
      have e1 : ∀ v : ℂ, ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp
          (Dg.comp (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c).restrictScalars ℝ).comp
            (Complex.conjCLE : ℂ →L[ℝ] ℂ)))) v = starRingEnd ℂ (Dg (starRingEnd ℂ v * c)) := by
        intro v
        simp [smul_eq_mul]
      rw [e1, e1, map_one, one_mul, Complex.conj_I]
      rw [c2br_clm_apply Dg c, c2br_clm_apply Dg (-Complex.I * c)]
      have hre : (-Complex.I * c).re = c.im := by simp
      have him : (-Complex.I * c).im = -c.re := by simp
      rw [hre, him, c2br_dbar_identity, norm_mul]
      have hGz : G z = starRingEnd ℂ (g w) := by simp only [hGdef, if_neg (not_le.2 hgt), hwdef]
      rw [hGz, Complex.norm_conj, Complex.norm_conj]
      have hc1 : ‖c‖ ≤ 1 := by
        rw [hcdef, norm_neg, norm_inv, norm_pow, Complex.norm_conj]
        exact inv_le_one_of_one_le₀ (one_le_pow₀ hgt.le)
      have hbound := hM w hwS
      calc ‖c‖ * ‖Dg 1 + Complex.I * Dg Complex.I‖ ≤ 1 * (|M| * ‖g w‖) := by
            gcongr
            exact hbound.trans (mul_le_mul_of_nonneg_right (le_abs_self M) (norm_nonneg _))
        _ = |M| * ‖g w‖ := one_mul _

end FiniteEnergyPlane

open FiniteEnergyPlane

theorem solution (g : ℂ → ℂ) (z₁ : ℂ)
    (hz₁ : z₁ ∈ sphere (0 : ℂ) 1) (r : ℝ) (hr : 0 < r)
    (hg : ContDiffOn ℝ 1 g (closedBall 0 1 ∩ ball z₁ r)) (M : ℝ)
    (hM : ∀ z ∈ ball (0 : ℂ) 1 ∩ ball z₁ r,
      ‖fderiv ℝ g z 1 + Complex.I * fderiv ℝ g z Complex.I‖ ≤ M * ‖g z‖)
    (hreal : ∀ z ∈ sphere (0 : ℂ) 1 ∩ ball z₁ r, (g z).im = 0) :
    ∃ ρ > (0 : ℝ), ∃ K : ℝ≥0, ∃ M' : ℝ,
      LipschitzOnWith K
        (fun z => if ‖z‖ ≤ 1 then g z else starRingEnd ℂ (g (starRingEnd ℂ z)⁻¹)) (ball z₁ ρ) ∧
      ∀ᵐ z ∂(volume.restrict (ball z₁ ρ)),
        ‖fderiv ℝ (fun z => if ‖z‖ ≤ 1 then g z else starRingEnd ℂ (g (starRingEnd ℂ z)⁻¹)) z 1 +
            Complex.I * fderiv ℝ
              (fun z => if ‖z‖ ≤ 1 then g z else starRingEnd ℂ (g (starRingEnd ℂ z)⁻¹)) z
              Complex.I‖ ≤
          M' * ‖(fun z => if ‖z‖ ≤ 1 then g z else starRingEnd ℂ (g (starRingEnd ℂ z)⁻¹)) z‖ :=
  exists_lipschitzOnWith_reflect_aux g z₁ hz₁ r hr hg M hM hreal
