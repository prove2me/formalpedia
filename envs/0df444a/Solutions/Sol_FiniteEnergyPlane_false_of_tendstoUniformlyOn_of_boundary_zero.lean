-- Prove2me | solution 1 for FiniteEnergyPlane.false_of_tendstoUniformlyOn_of_boundary_zero
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-27T00:17:54.205691+00:00
-- url     : https://prove2.me/submissions/ce96ac66-5392-44cb-9fea-b37ed2010b6d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_FiniteEnergyPlane_Setting
import Theorems.Thm_FiniteEnergyPlane_exists_lipschitzOnWith_reflect_of_norm_dbar_le
import Theorems.Thm_FiniteEnergyPlane_exists_hasLoopWind_of_lipschitzOnWith_norm_dbar_le
import Theorems.Thm_FiniteEnergyPlane_exists_eq_zero_of_hasLoopWind_of_norm_sub_lt



/-! Glue for `false_of_tendstoUniformlyOn_of_boundary_zero` over its children. -/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology
open scoped ContDiff NNReal

theorem c2b_norm_ccwLoop (R t : ℝ) (hR : 0 ≤ R) : ‖ccwLoop R t‖ = R := by
  simp only [ccwLoop, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR]
  rw [Complex.norm_exp_ofReal_mul_I, mul_one]

/-- `z ↦ (conj z)⁻¹` moves points outside the unit disc no farther from a point of the circle. -/
theorem c2b_norm_inv_conj_sub_le {z w : ℂ} (hz : 1 ≤ ‖z‖) (hw : ‖w‖ = 1) :
    ‖(starRingEnd ℂ z)⁻¹ - w‖ ≤ ‖z - w‖ := by
  have hz0 : z ≠ 0 := by rintro rfl; norm_num at hz
  have hw0 : w ≠ 0 := by rintro rfl; norm_num at hw
  have hwinv : (starRingEnd ℂ w)⁻¹ = w := by
    have : w * starRingEnd ℂ w = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hw]; norm_num
    rw [← inv_eq_of_mul_eq_one_right this, inv_inv]
  have hcz : starRingEnd ℂ z ≠ 0 := by simpa using hz0
  have hcw : starRingEnd ℂ w ≠ 0 := by simpa using hw0
  have key : (starRingEnd ℂ z)⁻¹ - w =
      (starRingEnd ℂ w - starRingEnd ℂ z) / (starRingEnd ℂ z * starRingEnd ℂ w) := by
    conv_lhs => rw [← hwinv]
    field_simp
  rw [key, norm_div, norm_mul, Complex.norm_conj, Complex.norm_conj, hw, mul_one,
    ← map_sub, Complex.norm_conj, norm_sub_rev]
  exact div_le_self (norm_nonneg _) hz

theorem false_of_tendstoUniformlyOn_of_boundary_zero_aux (g : ℂ → ℂ) (gn : ℕ → ℂ → ℂ) (z₁ : ℂ)
    (hz₁ : z₁ ∈ sphere (0 : ℂ) 1) (r : ℝ) (hr : 0 < r)
    (hg : ContDiffOn ℝ ∞ g (closedBall 0 1 ∩ ball z₁ r)) (M : ℝ)
    (hM : ∀ z ∈ ball (0 : ℂ) 1 ∩ ball z₁ r,
      ‖fderiv ℝ g z 1 + Complex.I * fderiv ℝ g z Complex.I‖ ≤ M * ‖g z‖)
    (hne : ∀ z ∈ ball (0 : ℂ) 1 ∩ ball z₁ r, g z ≠ 0)
    (hreal : ∀ z ∈ sphere (0 : ℂ) 1 ∩ ball z₁ r, (g z).im = 0) (hg₁ : g z₁ = 0)
    (hgn : ∀ n, ContinuousOn (gn n) (closedBall 0 1 ∩ ball z₁ r))
    (hgn_ne : ∀ n, ∀ z ∈ closedBall (0 : ℂ) 1 ∩ ball z₁ r, gn n z ≠ 0)
    (hgn_real : ∀ n, ∀ z ∈ sphere (0 : ℂ) 1 ∩ ball z₁ r, (gn n z).im = 0)
    (hconv : TendstoUniformlyOn gn g Filter.atTop (closedBall 0 1 ∩ ball z₁ r)) :
    False := by
  have hz₁n : ‖z₁‖ = 1 := by simpa using hz₁
  -- the reflection of a function across the unit circle
  set refl : (ℂ → ℂ) → ℂ → ℂ := fun f z =>
    if ‖z‖ ≤ 1 then f z else starRingEnd ℂ (f (starRingEnd ℂ z)⁻¹) with hrefl
  obtain ⟨ρ, hρ, K, M', hlip, hM'⟩ :=
    exists_lipschitzOnWith_reflect_of_norm_dbar_le g z₁ hz₁ r hr (hg.of_le (by norm_num)) M hM hreal
  have hG₁ : refl g z₁ = 0 := by simp [hrefl, hz₁n, hg₁]
  -- the reflected function is nonzero at interior points near `z₁`
  have hfreq : ∃ᶠ z in 𝓝 z₁, refl g z ≠ 0 := by
    rw [Filter.frequently_iff]
    intro U hU
    obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 hU
    set t : ℝ := min (min ε r) 1 / 2 with htdef
    have ht0 : 0 < t := by positivity
    have ht1 : t < 1 := by
      have : min (min ε r) 1 ≤ 1 := min_le_right _ _
      linarith
    have htε : t < ε := by
      have : min (min ε r) 1 ≤ ε := (min_le_left _ _).trans (min_le_left _ _)
      linarith
    have htr : t < r := by
      have : min (min ε r) 1 ≤ r := (min_le_left _ _).trans (min_le_right _ _)
      linarith
    set z : ℂ := ((1 - t : ℝ) : ℂ) * z₁ with hzdef
    have hzn : ‖z‖ = 1 - t := by
      rw [hzdef, norm_mul, hz₁n, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith)]
    have hzd : ‖z - z₁‖ = t := by
      have : z - z₁ = ((-t : ℝ) : ℂ) * z₁ := by rw [hzdef]; push_cast; ring
      rw [this, norm_mul, hz₁n, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_neg,
        abs_of_pos ht0]
    refine ⟨z, hεU ?_, ?_⟩
    · rw [mem_ball, dist_eq_norm, hzd]; exact htε
    · have hz1 : ‖z‖ ≤ 1 := by rw [hzn]; linarith
      simp only [hrefl, if_pos hz1]
      refine hne z ⟨?_, ?_⟩
      · rw [mem_ball, dist_zero_right, hzn]; linarith
      · rw [mem_ball, dist_eq_norm, hzd]; exact htr
  obtain ⟨m, hm, rW, hrW, hrWρ, hiso, hwind⟩ :=
    exists_hasLoopWind_of_lipschitzOnWith_norm_dbar_le (refl g) z₁ ρ hρ K hlip M' hM' hG₁ hfreq
  set R₀ : ℝ := min rW r / 2 with hR₀def
  have hR₀ : 0 < R₀ := by positivity
  have hR₀W : R₀ < rW := by
    have : min rW r ≤ rW := min_le_left _ _
    linarith
  have hR₀r : R₀ < r := by
    have : min rW r ≤ r := min_le_right _ _
    linarith
  -- points of `closedBall z₁ R₀` and their reflections lie in the domain
  have hin : ∀ z ∈ closedBall z₁ R₀, ‖z‖ ≤ 1 → z ∈ closedBall (0 : ℂ) 1 ∩ ball z₁ r :=
    fun z hz hz1 => ⟨by simpa using hz1, lt_of_le_of_lt (mem_closedBall.1 hz) hR₀r⟩
  have hout : ∀ z ∈ closedBall z₁ R₀, ¬ ‖z‖ ≤ 1 →
      (starRingEnd ℂ z)⁻¹ ∈ closedBall (0 : ℂ) 1 ∩ ball z₁ r := by
    intro z hz hz1
    push_neg at hz1
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall, dist_zero_right, norm_inv, Complex.norm_conj]
      exact inv_le_one_of_one_le₀ hz1.le
    · rw [mem_ball, dist_eq_norm]
      exact lt_of_le_of_lt (c2b_norm_inv_conj_sub_le hz1.le hz₁n)
        (lt_of_le_of_lt (by rw [← dist_eq_norm]; exact mem_closedBall.1 hz) hR₀r)
  -- the circle `sphere z₁ R₀`
  have hsph : ∀ t : ℝ, z₁ + ccwLoop R₀ t ∈ sphere z₁ R₀ := fun t => by
    rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, c2b_norm_ccwLoop R₀ t hR₀.le]
  have hsphW : sphere z₁ R₀ ⊆ ball z₁ ρ := fun z hz => by
    rw [mem_sphere] at hz
    rw [mem_ball, hz]
    linarith
  have hGne : ∀ z ∈ sphere z₁ R₀, refl g z ≠ 0 := by
    intro z hz
    refine hiso z ?_ ?_
    · rw [mem_ball, (mem_sphere.1 hz)]; exact hR₀W
    · rintro rfl; simp at hz; linarith
  -- a positive lower bound for `‖refl g‖` on the circle
  obtain ⟨z₂, hz₂, hmin⟩ := (isCompact_sphere z₁ R₀).exists_isMinOn
    ((NormedSpace.sphere_nonempty (E := ℂ) (x := z₁)).2 hR₀.le)
    ((hlip.continuousOn.mono hsphW).norm)
  set δ : ℝ := ‖refl g z₂‖ with hδdef
  have hδ : 0 < δ := norm_pos_iff.2 (hGne z₂ hz₂)
  obtain ⟨n, hn⟩ := (Metric.tendstoUniformlyOn_iff.1 hconv δ hδ).exists
  -- the reflected approximant vanishes somewhere on the closed disc
  have hcont : ContinuousOn (refl (gn n)) (closedBall z₁ R₀) := by
    refine ContinuousOn.if ?_ ?_ ?_
    · intro z hz
      have hz1 : ‖z‖ = 1 := by
        have := frontier_le_subset_eq continuous_norm continuous_const hz.2
        simpa using this
      have hzc : (starRingEnd ℂ z)⁻¹ = z := by
        have : z * starRingEnd ℂ z = 1 := by
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz1]; norm_num
        exact (inv_eq_of_mul_eq_one_left this)
      rw [hzc]
      have := hgn_real n z ⟨by simpa using hz1,
        lt_of_le_of_lt (mem_closedBall.1 hz.1) hR₀r⟩
      apply Complex.ext <;> simp [this]
    · refine (hgn n).mono ?_
      intro z hz
      refine hin z hz.1 ?_
      have h2 := hz.2
      rw [closure_le_eq (continuous_norm (E := ℂ)) continuous_const] at h2
      exact h2
    · have hsub : MapsTo (fun z => (starRingEnd ℂ z)⁻¹)
          (closedBall z₁ R₀ ∩ closure {z : ℂ | ¬ ‖z‖ ≤ 1}) (closedBall (0 : ℂ) 1 ∩ ball z₁ r) := by
        intro z hz
        have h1 : 1 ≤ ‖z‖ := by
          have := closure_lt_subset_le continuous_const continuous_norm
            (by simpa only [not_le] using hz.2)
          simpa using this
        refine ⟨?_, ?_⟩
        · rw [mem_closedBall, dist_zero_right, norm_inv, Complex.norm_conj]
          exact inv_le_one_of_one_le₀ h1
        · rw [mem_ball, dist_eq_norm]
          exact lt_of_le_of_lt (c2b_norm_inv_conj_sub_le h1 hz₁n)
            (lt_of_le_of_lt (by rw [← dist_eq_norm]; exact mem_closedBall.1 hz.1) hR₀r)
      have hinvc : ContinuousOn (fun z : ℂ => (starRingEnd ℂ z)⁻¹)
          (closedBall z₁ R₀ ∩ closure {z : ℂ | ¬ ‖z‖ ≤ 1}) := by
        refine ContinuousOn.inv₀ Complex.continuous_conj.continuousOn ?_
        intro z hz
        have h1 : 1 ≤ ‖z‖ := by
          have := closure_lt_subset_le continuous_const continuous_norm
            (by simpa only [not_le] using hz.2)
          simpa using this
        intro h0
        have : z = 0 := by simpa using h0
        rw [this, norm_zero] at h1
        linarith
      exact Complex.continuous_conj.comp_continuousOn ((hgn n).comp hinvc hsub)
  have hclose : ∀ t : ℝ, ‖refl (gn n) (z₁ + ccwLoop R₀ t) - refl g (z₁ + ccwLoop R₀ t)‖ <
      ‖refl g (z₁ + ccwLoop R₀ t)‖ := by
    intro t
    set z := z₁ + ccwLoop R₀ t
    have hzs := hsph t
    have hzb : z ∈ closedBall z₁ R₀ := sphere_subset_closedBall hzs
    refine lt_of_lt_of_le ?_ (hmin hzs)
    by_cases hz1 : ‖z‖ ≤ 1
    · simp only [hrefl, if_pos hz1]
      rw [norm_sub_rev, ← dist_eq_norm]
      exact hn z (hin z hzb hz1)
    · simp only [hrefl, if_neg hz1]
      rw [← map_sub, Complex.norm_conj, norm_sub_rev, ← dist_eq_norm]
      exact hn _ (hout z hzb hz1)
  obtain ⟨z, hz, hz0⟩ := exists_eq_zero_of_hasLoopWind_of_norm_sub_lt (refl (gn n)) (refl g) z₁ R₀
    hR₀ hcont m (by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hm)) (hwind R₀ ⟨hR₀, hR₀W⟩) hclose
  by_cases hz1 : ‖z‖ ≤ 1
  · simp only [hrefl, if_pos hz1] at hz0
    exact hgn_ne n z (hin z hz hz1) hz0
  · simp only [hrefl, if_neg hz1, map_eq_zero] at hz0
    exact hgn_ne n _ (hout z hz hz1) hz0

end FiniteEnergyPlane

open FiniteEnergyPlane

open Metric
open scoped ContDiff

theorem solution (g : ℂ → ℂ) (gn : ℕ → ℂ → ℂ) (z₁ : ℂ)
    (hz₁ : z₁ ∈ sphere (0 : ℂ) 1) (r : ℝ) (hr : 0 < r)
    (hg : ContDiffOn ℝ ∞ g (closedBall 0 1 ∩ ball z₁ r)) (M : ℝ)
    (hM : ∀ z ∈ ball (0 : ℂ) 1 ∩ ball z₁ r,
      ‖fderiv ℝ g z 1 + Complex.I * fderiv ℝ g z Complex.I‖ ≤ M * ‖g z‖)
    (hne : ∀ z ∈ ball (0 : ℂ) 1 ∩ ball z₁ r, g z ≠ 0)
    (hreal : ∀ z ∈ sphere (0 : ℂ) 1 ∩ ball z₁ r, (g z).im = 0) (hg₁ : g z₁ = 0)
    (hgn : ∀ n, ContinuousOn (gn n) (closedBall 0 1 ∩ ball z₁ r))
    (hgn_ne : ∀ n, ∀ z ∈ closedBall (0 : ℂ) 1 ∩ ball z₁ r, gn n z ≠ 0)
    (hgn_real : ∀ n, ∀ z ∈ sphere (0 : ℂ) 1 ∩ ball z₁ r, (gn n z).im = 0)
    (hconv : TendstoUniformlyOn gn g Filter.atTop (closedBall 0 1 ∩ ball z₁ r)) :
    False :=
  false_of_tendstoUniformlyOn_of_boundary_zero_aux g gn z₁ hz₁ r hr hg M hM hne hreal hg₁ hgn hgn_ne hgn_real hconv
