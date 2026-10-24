-- Prove2me | solution 1 for FiniteEnergyPlane.energy_ge_of_almostComplex
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-23T17:01:38.928912+00:00
-- url     : https://prove2.me/submissions/c428ccf2-9587-4931-8451-24c1538471ac

import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.Complex.ExponentialBounds
import Theorems.Thm_FiniteEnergyPlane_monotoneOn_energy_ratio
import Theorems.Thm_FiniteEnergyPlane_exists_cutoff



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal

set_option maxHeartbeats 1000000 in
/-- Monotonicity lemma near a complex structure on a real inner product space. Let `J₀` be a
complex structure with `‖J₀‖ ≤ β`. There are `c, κ > 0` (depending on `β` and `F`) such that the
following holds. Let `Λ ≥ 0`, `S > 0` with `Λ S ≤ κ`, `q ∈ F`, `U ⊆ ℂ` open and `u` a `C²` map on
`U` with `∂ₜu = A(z) ∂ₛu` and `‖A(z) - J₀‖ ≤ Λ ‖u z - q‖` wherever `‖u z - q‖ < S`. Assume the sets
`{z ∈ U | ‖u z - q‖ ≤ ρ}` are compact for `ρ < S`, and `u z₁ = q`, `Du(z₁) ≠ 0` for some
`z₁ ∈ U`. Then `∫_U ‖Du‖² ≥ c S²`. -/
theorem energy_ge_of_almostComplex_aux {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (β : ℝ) :
    ∃ c > 0, ∃ κ > 0, ∀ J₀ : F →L[ℝ] F, J₀.comp J₀ = -ContinuousLinearMap.id ℝ F → ‖J₀‖ ≤ β →
      ∀ Λ S : ℝ, 0 ≤ Λ → 0 < S → Λ * S ≤ κ →
      ∀ (q : F) (U : Set ℂ) (u : ℂ → F) (A : ℂ → F →L[ℝ] F), IsOpen U → ContDiffOn ℝ 2 u U →
      (∀ z ∈ U, ‖u z - q‖ < S → fderiv ℝ u z Complex.I = A z (fderiv ℝ u z 1) ∧
        ‖A z - J₀‖ ≤ Λ * ‖u z - q‖) →
      (∀ ρ, ρ < S → IsCompact {z | z ∈ U ∧ ‖u z - q‖ ≤ ρ}) →
      (∃ z₁ ∈ U, u z₁ = q ∧ fderiv ℝ u z₁ ≠ 0) →
      ENNReal.ofReal (c * S ^ 2) ≤ ∫⁻ z in U, ENNReal.ofReal (‖fderiv ℝ u z‖ ^ 2) := by
  set b := max β 1 with hb
  have hb1 : 1 ≤ b := le_max_right _ _
  have hb0 : 0 < b := by linarith
  refine ⟨1 / (50 * (2 + b) ^ 2 * (1 + b ^ 2) ^ 3 * b), by positivity,
    1 / (4 * (1 + b ^ 2) ^ 2 * b), by positivity, ?_⟩
  intro J₀ hJ hJβ Λ S hΛ hS hΛS q U u A hU hu hhol hprop hz₁
  have hJb : ‖J₀‖ ≤ b := hJβ.trans (le_max_left _ _)
  obtain ⟨φ, hφc, hφ1, hφ0, hφb, hφd, hφd0, Mφ, hMφ⟩ := exists_cutoff
  obtain ⟨hΦ, hmono⟩ := monotoneOn_energy_ratio J₀ hJ hb1 hJb hΛ hS hΛS q A hU hu hhol hprop
    hφc hφ0 hφb hφd hφd0 hMφ
  set γ := 1 + b ^ 2 with hγ
  have hγ1 : 1 ≤ γ := by nlinarith
  have hγ0 : 0 < γ := by linarith
  set C := (γ * b + 2 * γ ^ 2 * b) * Λ with hC
  have hC0 : 0 ≤ C := by positivity
  have hCS : C * S ≤ 3 / 4 := by
    have h1 : C * S = (γ * b + 2 * γ ^ 2 * b) * (Λ * S) := by rw [hC]; ring
    have h2 : (γ * b + 2 * γ ^ 2 * b) * (Λ * S) ≤ (γ * b + 2 * γ ^ 2 * b) * (1 / (4 * γ ^ 2 * b)) :=
      mul_le_mul_of_nonneg_left hΛS (by positivity)
    have h3 : (γ * b + 2 * γ ^ 2 * b) * (1 / (4 * γ ^ 2 * b)) = 1 / (4 * γ) + 1 / 2 := by
      field_simp; try ring
    have h4 : 1 / (4 * γ) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  have hJJ : ∀ v, J₀ (J₀ v) = -v := fun v => by
    simpa using congrArg (fun T : F →L[ℝ] F => T v) hJ
  have hJn : ∀ v, ‖J₀ v‖ ≤ b * ‖v‖ := fun v =>
    (J₀.le_opNorm v).trans (mul_le_mul_of_nonneg_right hJb (norm_nonneg _))
  let gB : F →L[ℝ] F →L[ℝ] ℝ := innerSL ℝ + (innerSL ℝ).bilinearComp J₀ J₀
  have hg : ∀ v v', gB v v' = inner ℝ v v' + inner ℝ (J₀ v) (J₀ v') := fun v v' => rfl
  let σ : F →L[ℝ] F →L[ℝ] ℝ := gB.comp J₀
  have hσ : ∀ v v', σ v v' = gB (J₀ v) v' := fun v v' => rfl
  have hgN : ∀ v, ‖v‖ ^ 2 ≤ gB v v := fun v => by
    rw [hg, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    nlinarith [sq_nonneg ‖J₀ v‖]
  have hgU : ∀ v, gB v v ≤ γ * ‖v‖ ^ 2 := fun v => by
    rw [hg, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    have h2 : ‖J₀ v‖ ^ 2 ≤ (b * ‖v‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hJn v) 2
    nlinarith
  have hgle : ∀ v v', |gB v v'| ≤ γ * ‖v‖ * ‖v'‖ := by
    intro v v'
    have h1 := abs_real_inner_le_norm v v'
    have h2 := abs_real_inner_le_norm (J₀ v) (J₀ v')
    have h4 : ‖J₀ v‖ * ‖J₀ v'‖ ≤ b * ‖v‖ * (b * ‖v'‖) :=
      mul_le_mul (hJn v) (hJn v') (norm_nonneg _) (by positivity)
    rw [hg]
    calc |inner ℝ v v' + inner ℝ (J₀ v) (J₀ v')| ≤ ‖v‖ * ‖v'‖ + ‖J₀ v‖ * ‖J₀ v'‖ :=
          (abs_add_le _ _).trans (add_le_add h1 h2)
      _ ≤ γ * ‖v‖ * ‖v'‖ := by rw [hγ]; nlinarith [mul_nonneg (norm_nonneg v) (norm_nonneg v')]
  set f : ℂ → ℝ := fun z => inner ℝ (u z - q) (u z - q) + inner ℝ (J₀ (u z - q)) (J₀ (u z - q))
    with hf
  set a : ℂ → ℝ := fun z => inner ℝ (J₀ (fderiv ℝ u z 1)) (fderiv ℝ u z Complex.I) +
    inner ℝ (J₀ (J₀ (fderiv ℝ u z 1))) (J₀ (fderiv ℝ u z Complex.I)) with ha
  set I : ℝ → ℝ := fun s => ∫ z, U.indicator (fun z => φ ((s ^ 2)⁻¹ * f z)) z * a z with hI
  have hu1 : ContDiffOn ℝ 1 (fderiv ℝ u) U := hu.fderiv_of_isOpen hU (by norm_num)
  have hDu : ∀ z ∈ U, HasFDerivAt u (fderiv ℝ u z) z := fun z hz =>
    ((hu.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num)).hasFDerivAt
  have hacont : ContinuousOn a U :=
    ((σ.continuous.comp_continuousOn (hu1.continuousOn.clm_apply continuousOn_const))).clm_apply
      (hu1.continuousOn.clm_apply continuousOn_const)
  have hI0 : ∀ s, 0 < s → s < S → 0 ≤ I s := fun s hs hsS =>
    integral_nonneg (hΦ s ⟨hs, hsS⟩).2
  -- the regular point `z₁`
  obtain ⟨z₁, hz₁U, hz₁q, hL⟩ := hz₁
  have hz₁S : ‖u z₁ - q‖ < S := by simp [hz₁q, hS]
  set L := fderiv ℝ u z₁ with hLdef
  set x₁ := L 1 with hx₁
  have hA₁ : A z₁ = J₀ := by
    have h := (hhol z₁ hz₁U hz₁S).2
    rw [hz₁q, sub_self, norm_zero, mul_zero] at h
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h)
  have hLI : L Complex.I = J₀ x₁ := by
    rw [hx₁, ← hA₁]; exact (hhol z₁ hz₁U hz₁S).1
  have hLh : ∀ h : ℂ, L h = h.re • x₁ + h.im • J₀ x₁ := by
    intro h
    have e : h = h.re • (1 : ℂ) + h.im • Complex.I := by
      apply Complex.ext <;> simp
    conv_lhs => rw [e]
    rw [map_add, map_smul, map_smul, hLI]
  have hx₁0 : x₁ ≠ 0 := by
    intro h0; apply hL
    ext h
    rw [hLh, h0]; simp
  set n1 := ‖x₁‖ with hn1
  have hn1pos : 0 < n1 := norm_pos_iff.2 hx₁0
  have hLn : ‖L‖ ≤ (1 + b) * n1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun h => ?_)
    rw [hLh]
    calc ‖h.re • x₁ + h.im • J₀ x₁‖ ≤ |h.re| * n1 + |h.im| * (b * n1) := by
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [norm_smul, Real.norm_eq_abs]
          · rw [norm_smul, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_left (hJn x₁) (abs_nonneg _)
      _ ≤ ‖h‖ * n1 + ‖h‖ * (b * n1) :=
          add_le_add (mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm h) hn1pos.le)
            (mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm h) (by positivity))
      _ = (1 + b) * n1 * ‖h‖ := by ring
  have hLo := (hasFDerivAt_iff_isLittleO.1 (hDu z₁ hz₁U)).def hn1pos
  have hw1 : ∀ᶠ z in 𝓝 z₁, ‖u z - q‖ ≤ (2 + b) * n1 * ‖z - z₁‖ := by
    filter_upwards [hLo] with z hz
    have e : u z - q = (u z - u z₁ - L (z - z₁)) + L (z - z₁) := by rw [hz₁q]; abel
    rw [e]
    calc ‖(u z - u z₁ - L (z - z₁)) + L (z - z₁)‖ ≤ n1 * ‖z - z₁‖ + ‖L‖ * ‖z - z₁‖ :=
          (norm_add_le _ _).trans (add_le_add hz (L.le_opNorm _))
      _ ≤ n1 * ‖z - z₁‖ + (1 + b) * n1 * ‖z - z₁‖ := by
          gcongr
      _ = (2 + b) * n1 * ‖z - z₁‖ := by ring
  set m2 := gB x₁ x₁ with hm2
  have hm2n : n1 ^ 2 ≤ m2 := hgN x₁
  have ha₁ : a z₁ = m2 := by
    show σ x₁ (L Complex.I) = gB x₁ x₁
    rw [hLI, hσ, hg, hg, hJJ, inner_neg_neg]; ring
  have ha_ev : ∀ᶠ z in 𝓝 z₁, m2 / 2 < a z :=
    (hacont.continuousAt (hU.mem_nhds hz₁U)).eventually
      (lt_mem_nhds (by rw [ha₁]; nlinarith [sq_pos_of_pos hn1pos]))
  obtain ⟨ρ, hρ, hρball⟩ :=
    Metric.eventually_nhds_iff_ball.1 ((hU.eventually_mem hz₁U).and (hw1.and ha_ev))
  set c₀ := 1 / (4 * (2 + b) ^ 2 * γ ^ 2) with hc₀
  have hsmall : ∀ s, 0 < s → s < min (S / 2) (2 * (2 + b) * γ * n1 * ρ) → c₀ * s ^ 2 ≤ I s := by
    intro s hs hs'
    have hsS : s < S := by linarith [min_le_left (S / 2) (2 * (2 + b) * γ * n1 * ρ)]
    have hsρ : s < 2 * (2 + b) * γ * n1 * ρ := hs'.trans_le (min_le_right _ _)
    set r := s / (2 * (2 + b) * γ * n1) with hr
    have hr0 : 0 < r := by positivity
    have hrρ : r < ρ := by
      rw [hr, div_lt_iff₀ (by positivity)]; linarith
    have hon : ∀ z ∈ ball z₁ r, n1 ^ 2 / 2 ≤ U.indicator (fun z => φ ((s ^ 2)⁻¹ * f z)) z * a z := by
      intro z hz
      obtain ⟨hzU, hzw, hza⟩ := hρball z (ball_subset_ball hrρ.le hz)
      have hd : ‖z - z₁‖ < r := by rwa [mem_ball, dist_eq_norm] at hz
      have hw : ‖u z - q‖ ≤ s / (2 * γ) := by
        calc ‖u z - q‖ ≤ (2 + b) * n1 * ‖z - z₁‖ := hzw
          _ ≤ (2 + b) * n1 * r := by gcongr
          _ = s / (2 * γ) := by rw [hr]; field_simp
      have hfz : (s ^ 2)⁻¹ * f z ≤ 1 / 4 := by
        have h1 : f z ≤ γ * (s / (2 * γ)) ^ 2 :=
          (hgU _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hw 2) hγ0.le)
        have h2 : γ * (s / (2 * γ)) ^ 2 ≤ s ^ 2 / 4 := by
          have e : γ * (s / (2 * γ)) ^ 2 = s ^ 2 / 4 * (1 / γ) := by field_simp; ring
          have : 1 / γ ≤ 1 := by rw [div_le_one hγ0]; exact hγ1
          rw [e]
          exact mul_le_of_le_one_right (by positivity) this
        rw [inv_mul_le_iff₀ (by positivity)]; linarith only [h1, h2]
      simp only [indicator_of_mem hzU, hφ1 _ hfz, one_mul]
      linarith
    have hint := (hΦ s ⟨hs, hsS⟩).1
    have h1 : ∫ z in ball z₁ r, U.indicator (fun z => φ ((s ^ 2)⁻¹ * f z)) z * a z ≤ I s :=
      setIntegral_le_integral hint (Filter.Eventually.of_forall (hΦ s ⟨hs, hsS⟩).2)
    have h2 : ∫ z in ball z₁ r, (n1 ^ 2 / 2 : ℝ) ≤
        ∫ z in ball z₁ r, U.indicator (fun z => φ ((s ^ 2)⁻¹ * f z)) z * a z :=
      setIntegral_mono_on (integrableOn_const (measure_ball_lt_top).ne) hint.integrableOn
        measurableSet_ball hon
    have hvol : (volume (ball z₁ r)).toReal = r ^ 2 * Real.pi := by
      rw [Complex.volume_ball, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr0.le]
      simp
    rw [setIntegral_const, Measure.real, hvol, smul_eq_mul] at h2
    have h3 : c₀ * s ^ 2 ≤ r ^ 2 * Real.pi * (n1 ^ 2 / 2) := by
      have e : r ^ 2 * Real.pi * (n1 ^ 2 / 2) =
          s ^ 2 / (4 * (2 + b) ^ 2 * γ ^ 2) * (Real.pi / 2) := by
        rw [hr]; field_simp; ring
      rw [e, hc₀]
      have hpi : 1 ≤ Real.pi / 2 := by linarith [Real.two_le_pi]
      have : 0 ≤ s ^ 2 / (4 * (2 + b) ^ 2 * γ ^ 2) := by positivity
      rw [show 1 / (4 * (2 + b) ^ 2 * γ ^ 2) * s ^ 2 = s ^ 2 / (4 * (2 + b) ^ 2 * γ ^ 2) by ring]
      nlinarith
    linarith
  -- transport to `s = S / 2` by monotonicity
  set s₁ := min (S / 2) (2 * (2 + b) * γ * n1 * ρ) with hs₁
  have hs₁0 : 0 < s₁ := lt_min (by linarith) (by positivity)
  have hs₁S : s₁ ≤ S / 2 := min_le_left _ _
  have hlow := hsmall (s₁ / 2) (by linarith) (by linarith)
  have hm : Real.exp (2 * C * (s₁ / 2)) * I (s₁ / 2) / (s₁ / 2) ^ 2 ≤
      Real.exp (2 * C * (S / 2)) * I (S / 2) / (S / 2) ^ 2 :=
    hmono ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (show s₁ / 2 ≤ S / 2 by linarith)
  have h1 : c₀ ≤ Real.exp (2 * C * (s₁ / 2)) * I (s₁ / 2) / (s₁ / 2) ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have : 1 ≤ Real.exp (2 * C * (s₁ / 2)) := Real.one_le_exp (by positivity)
    nlinarith [hI0 (s₁ / 2) (by linarith) (by linarith)]
  have hexp : Real.exp (2 * C * (S / 2)) ≤ 3 := by
    have : 2 * C * (S / 2) ≤ 1 := by nlinarith [hCS]
    calc Real.exp (2 * C * (S / 2)) ≤ Real.exp 1 := Real.exp_le_exp.2 this
      _ ≤ 3 := Real.exp_one_lt_d9.le.trans (by norm_num)
  have hIS : c₀ * (S / 2) ^ 2 / 3 ≤ I (S / 2) := by
    have h2 := h1.trans hm
    rw [le_div_iff₀ (by positivity)] at h2
    rw [div_le_iff₀ (by norm_num)]
    nlinarith [mul_le_mul_of_nonneg_right hexp (hI0 (S / 2) (by linarith) (by linarith))]
  -- comparison with the Dirichlet energy
  have hIle : ENNReal.ofReal (I (S / 2)) ≤
      ENNReal.ofReal (γ * b) * ∫⁻ z in U, ENNReal.ofReal (‖fderiv ℝ u z‖ ^ 2) := by
    have hint := (hΦ (S / 2) ⟨by linarith, by linarith⟩).1
    rw [show I (S / 2) = ∫ z, U.indicator (fun z => φ (((S / 2) ^ 2)⁻¹ * f z)) z * a z from rfl,
      ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall (hΦ (S / 2) ⟨by linarith, by linarith⟩).2),
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_indicator hU.measurableSet]
    refine lintegral_mono (fun z => ?_)
    by_cases hz : z ∈ U
    · simp only [indicator_of_mem hz]
      rw [← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hx : ‖fderiv ℝ u z 1‖ ≤ ‖fderiv ℝ u z‖ := by
        simpa using (fderiv ℝ u z).le_opNorm 1
      have hy : ‖fderiv ℝ u z Complex.I‖ ≤ ‖fderiv ℝ u z‖ := by
        simpa using (fderiv ℝ u z).le_opNorm Complex.I
      have hal : a z ≤ γ * b * ‖fderiv ℝ u z‖ ^ 2 := by
        have h1 : a z ≤ γ * ‖J₀ (fderiv ℝ u z 1)‖ * ‖fderiv ℝ u z Complex.I‖ :=
          (le_abs_self (gB (J₀ (fderiv ℝ u z 1)) (fderiv ℝ u z Complex.I))).trans (hgle _ _)
        have h2 : ‖J₀ (fderiv ℝ u z 1)‖ * ‖fderiv ℝ u z Complex.I‖ ≤
            b * ‖fderiv ℝ u z‖ * ‖fderiv ℝ u z‖ :=
          mul_le_mul ((hJn _).trans (mul_le_mul_of_nonneg_left hx hb0.le)) hy (norm_nonneg _)
            (by positivity)
        calc a z ≤ γ * ‖J₀ (fderiv ℝ u z 1)‖ * ‖fderiv ℝ u z Complex.I‖ := h1
          _ = γ * (‖J₀ (fderiv ℝ u z 1)‖ * ‖fderiv ℝ u z Complex.I‖) := by ring
          _ ≤ γ * (b * ‖fderiv ℝ u z‖ * ‖fderiv ℝ u z‖) := mul_le_mul_of_nonneg_left h2 hγ0.le
          _ = γ * b * ‖fderiv ℝ u z‖ ^ 2 := by ring
      have hφ' := hφb (((S / 2) ^ 2)⁻¹ * f z)
      have hnn : 0 ≤ γ * b * ‖fderiv ℝ u z‖ ^ 2 := by positivity
      rcases le_or_gt 0 (a z) with ha0 | ha0
      · calc φ (((S / 2) ^ 2)⁻¹ * f z) * a z ≤ 1 * a z := mul_le_mul_of_nonneg_right hφ'.2 ha0
          _ ≤ γ * b * ‖fderiv ℝ u z‖ ^ 2 := by rw [one_mul]; exact hal
      · exact (mul_nonpos_of_nonneg_of_nonpos hφ'.1 ha0.le).trans hnn
    · simp [hz]
  have hfin : ENNReal.ofReal (1 / (50 * (2 + b) ^ 2 * γ ^ 3 * b) * S ^ 2) *
      ENNReal.ofReal (γ * b) ≤ ENNReal.ofReal (I (S / 2)) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    refine le_trans ?_ hIS
    have e1 : 1 / (50 * (2 + b) ^ 2 * γ ^ 3 * b) * S ^ 2 * (γ * b) =
        S ^ 2 / ((2 + b) ^ 2 * γ ^ 2) * (1 / 50) := by field_simp; try ring
    have e2 : c₀ * (S / 2) ^ 2 / 3 = S ^ 2 / ((2 + b) ^ 2 * γ ^ 2) * (1 / 48) := by
      rw [hc₀]; field_simp; try ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left (by norm_num) (by positivity)
  have hpos : ENNReal.ofReal (γ * b) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
  refine (ENNReal.mul_le_mul_iff_right hpos ENNReal.ofReal_ne_top).1 ?_
  rw [mul_comm]
  exact hfin.trans hIle


end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal

theorem solution {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (β : ℝ) :
    ∃ c > 0, ∃ κ > 0, ∀ J₀ : F →L[ℝ] F, J₀.comp J₀ = -ContinuousLinearMap.id ℝ F → ‖J₀‖ ≤ β →
      ∀ Λ S : ℝ, 0 ≤ Λ → 0 < S → Λ * S ≤ κ →
      ∀ (q : F) (U : Set ℂ) (u : ℂ → F) (A : ℂ → F →L[ℝ] F), IsOpen U → ContDiffOn ℝ 2 u U →
      (∀ z ∈ U, ‖u z - q‖ < S → fderiv ℝ u z Complex.I = A z (fderiv ℝ u z 1) ∧
        ‖A z - J₀‖ ≤ Λ * ‖u z - q‖) →
      (∀ ρ, ρ < S → IsCompact {z | z ∈ U ∧ ‖u z - q‖ ≤ ρ}) →
      (∃ z₁ ∈ U, u z₁ = q ∧ fderiv ℝ u z₁ ≠ 0) →
      ENNReal.ofReal (c * S ^ 2) ≤ ∫⁻ z in U, ENNReal.ofReal (‖fderiv ℝ u z‖ ^ 2) :=
  energy_ge_of_almostComplex_aux β
