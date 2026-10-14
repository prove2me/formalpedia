-- Prove2me | solution 1 for DbarRegularity.norm_fourier_le_of_hormander
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T17:51:43.759108+00:00
-- url     : https://prove2.me/submissions/00ec1589-4c75-47ef-abb2-e19ad99258e3

import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Theorems.Thm_DbarRegularity_lintegral_indicator_sub_le
import Theorems.Thm_DbarRegularity_integral_ball_norm_rpow_one_sub



namespace DbarRegularity

open MeasureTheory Set Metric FourierTransform
open scoped ENNReal Real RealInnerProductSpace

/-- The Fourier transform of an integrable kernel with `|K(x)| ≤ B |x|^{-d}`, Hörmander constant
`B₁` and vanishing integrals over all balls `B(0, r)` is bounded by `C (B + B₁)`, with `C`
depending only on `d`. -/
theorem norm_fourier_le_of_hormander {d : ℕ} (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (K : EuclideanSpace ℝ (Fin d) → ℂ) (B B₁ : ℝ), 0 ≤ B₁ →
      Integrable K volume →
      (∀ x, x ≠ 0 → ‖K x‖ ≤ B / ‖x‖ ^ d) →
      (∀ y, y ≠ 0 → ∫⁻ x in {x | 2 * ‖y‖ ≤ ‖x‖}, ‖K (x - y) - K x‖ₑ ≤ ENNReal.ofReal B₁) →
      (∀ r : ℝ, 0 < r → ∫ x in ball 0 r, K x = 0) →
      ∀ ξ, ‖𝓕 K ξ‖ ≤ C * (B + B₁) := by
  set V := EuclideanSpace ℝ (Fin d)
  haveI : NeZero d := ⟨hd.ne'⟩
  obtain ⟨CH, hCH0, hCH⟩ := lintegral_indicator_sub_le hd
  set Vr : ℝ := volume.real (ball (0 : V) 1)
  have hVr : 0 ≤ Vr := ENNReal.toReal_nonneg
  refine ⟨2 * π * d * Vr + CH + Vr + 1, by positivity, ?_⟩
  intro K B B₁ hB₁ hKi hK1 hK2 hK3 ξ
  -- `B ≥ 0`
  have hB : 0 ≤ B := by
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    have := (norm_nonneg _).trans (hK1 x hx)
    exact (div_nonneg_iff.1 this).elim (fun h => h.1)
      (fun h => absurd h.2 (not_le.2 (by have := norm_pos_iff.2 hx; positivity)))
  have hfin : Module.finrank ℝ V = d := finrank_euclideanSpace_fin
  -- the character
  set e : V → ℂ := fun x => ((𝐞 (-⟪x, ξ⟫) : Circle) : ℂ) with he
  have he_norm : ∀ x, ‖e x‖ = 1 := fun x => Circle.norm_coe _
  have hF : 𝓕 K ξ = ∫ x, e x * K x := by
    rw [Real.fourier_eq]; simp [he, Circle.smul_def]; rfl
  have heK : Integrable (fun x => e x * K x) volume := by
    have := (Real.fourierIntegral_convergent_iff (μ := volume) (f := K) ξ).2 hKi
    simpa [he, Circle.smul_def] using this
  by_cases hξ : ξ = 0
  · -- `𝓕 K 0 = ∫ K = 0`
    have hint : ∫ x, K x = 0 := by
      have hmono : Monotone (fun n : ℕ => ball (0 : V) n) := fun m n hmn =>
        ball_subset_ball (by exact_mod_cast hmn)
      have ht := tendsto_setIntegral_of_monotone (μ := volume) (fun n => measurableSet_ball) hmono
        hKi.integrableOn
      rw [iUnion_ball_nat, Measure.restrict_univ] at ht
      refine tendsto_nhds_unique ht ?_
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      exact (hK3 n (by exact_mod_cast hn)).symm
    have he1 : ∀ x, e x = 1 := by intro x; simp [he, hξ]
    rw [hF]
    simp_rw [he1, one_mul]
    rw [hint, norm_zero]
    positivity
  have hξ0 : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  set ρ : ℝ := ‖ξ‖⁻¹ with hρ
  have hρ0 : 0 < ρ := inv_pos.2 hξ0
  -- split at radius `ρ`
  have hsplit := integral_add_compl (measurableSet_ball (x := (0 : V)) (ε := ρ)) heK
  -- inner part
  have hI₁ : ‖∫ x in ball (0 : V) ρ, e x * K x‖ ≤ 2 * π * d * Vr * B := by
    have h0 : ∫ x in ball (0 : V) ρ, e x * K x =
        ∫ x in ball (0 : V) ρ, (e x - 1) * K x := by
      simp_rw [sub_mul, one_mul]
      rw [integral_sub heK.integrableOn hKi.integrableOn, hK3 ρ hρ0, sub_zero]
    rw [h0]
    obtain ⟨hgi, hgv⟩ := integral_ball_norm_rpow_one_sub hd ρ hρ0
    have hae : ∀ᵐ x ∂(volume.restrict (ball (0 : V) ρ)), ‖(e x - 1) * K x‖ ≤
        (2 * π * ‖ξ‖ * B) * ‖x‖ ^ (1 - d : ℝ) := by
      refine ae_restrict_of_ae ?_
      have h0 : ∀ᵐ x ∂(volume : Measure V), x ≠ 0 := by
        rw [ae_iff]; simp [measure_singleton]
      filter_upwards [h0] with x hx
      have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx
      rw [norm_mul]
      have hexp : ‖e x - 1‖ ≤ 2 * π * ‖x‖ * ‖ξ‖ := by
        have : e x = Complex.exp (Complex.I * ↑(2 * π * (-⟪x, ξ⟫))) := by
          simp only [he, Real.fourierChar_apply]; ring_nf
        rw [this]
        refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
        rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos (by positivity)]
        have := abs_real_inner_le_norm x ξ
        nlinarith [Real.pi_pos]
      calc ‖e x - 1‖ * ‖K x‖ ≤ (2 * π * ‖x‖ * ‖ξ‖) * (B / ‖x‖ ^ d) :=
            mul_le_mul hexp (hK1 x hx) (norm_nonneg _) (by positivity)
        _ = (2 * π * ‖ξ‖ * B) * ‖x‖ ^ (1 - d : ℝ) := by
            rw [Real.rpow_sub hxpos, Real.rpow_one, Real.rpow_natCast]
            ring
    calc _ ≤ ∫ x in ball (0 : V) ρ, (2 * π * ‖ξ‖ * B) * ‖x‖ ^ (1 - d : ℝ) :=
          norm_integral_le_of_norm_le (hgi.const_mul _) hae
      _ = 2 * π * d * Vr * B := by
          rw [integral_const_mul, hgv, hρ]
          field_simp
          rfl
  -- outer part: the truncated kernel
  set J : V → ℂ := {x | ρ ≤ ‖x‖}.indicator K with hJ
  have hJi : Integrable J volume :=
    hKi.indicator (measurableSet_le measurable_const measurable_norm)
  have hcompl : ∫ x in (ball (0 : V) ρ)ᶜ, e x * K x = ∫ x, e x * J x := by
    have : (ball (0 : V) ρ)ᶜ = {x | ρ ≤ ‖x‖} := by
      ext x; simp [mem_ball_zero_iff]
    rw [this, ← integral_indicator (measurableSet_le measurable_const measurable_norm)]
    congr 1; ext x
    simp only [hJ, indicator]
    split_ifs <;> simp
  set z : V := (2 * ‖ξ‖ ^ 2)⁻¹ • ξ with hz
  have hzξ : ⟪z, ξ⟫ = 1 / 2 := by
    rw [hz, real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
  have hznorm : ‖z‖ = ρ / 2 := by
    rw [hz, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), hρ]
    field_simp
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hznorm; linarith
  have he_shift : ∀ x, e (x - z) = - e x := by
    intro x
    simp only [he, inner_sub_left, hzξ, neg_sub]
    rw [sub_eq_add_neg, AddChar.map_add_eq_mul]
    have : (𝐞 (1 / 2 : ℝ) : ℂ) = -1 := by
      rw [Real.fourierChar_apply]
      have : (↑(2 * π * (1 / 2 : ℝ)) * Complex.I) = π * Complex.I := by push_cast; ring
      rw [this, Complex.exp_pi_mul_I]
    rw [Circle.coe_mul, this]
    ring_nf
  have hJz : Integrable (fun x => J (x - z)) volume := hJi.comp_sub_right z
  have heJ : Integrable (fun x => e x * J x) volume := by
    have := (Real.fourierIntegral_convergent_iff (μ := volume) (f := J) ξ).2 hJi
    simpa [he, Circle.smul_def] using this
  have heJz : Integrable (fun x => e x * J (x - z)) volume := by
    have := (Real.fourierIntegral_convergent_iff (μ := volume) (f := fun x => J (x - z)) ξ).2 hJz
    simpa [he, Circle.smul_def] using this
  have h2 : 2 * ∫ x, e x * J x = ∫ x, e x * (J x - J (x - z)) := by
    have hshift : ∫ x, e x * J x = - ∫ x, e x * J (x - z) := by
      rw [← integral_sub_right_eq_self (fun x => e x * J x) z, ← integral_neg]
      congr 1; ext x; rw [he_shift]; ring
    simp_rw [mul_sub]
    rw [integral_sub heJ heJz, hshift]
    ring
  -- estimate of the outer part
  set S : Set V := {x | 2 * ‖z‖ ≤ ‖x‖}
  have hS : MeasurableSet S := measurableSet_le measurable_const measurable_norm
  have hSeq : S = {x | ρ ≤ ‖x‖} := by
    ext x; simp only [S, mem_setOf_eq, hznorm]; ring_nf
  have hout : ‖∫ x, e x * (J x - J (x - z))‖ₑ ≤
      ENNReal.ofReal B₁ + ENNReal.ofReal (CH * B) + ENNReal.ofReal (Vr * B) := by
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    have hn : ∀ x, ‖e x * (J x - J (x - z))‖ₑ = ‖J (x - z) - J x‖ₑ := by
      intro x
      rw [enorm_mul, ← ofReal_norm_eq_enorm (e x), he_norm, ENNReal.ofReal_one, one_mul,
        ← enorm_neg, neg_sub]
    simp_rw [hn]
    rw [← lintegral_add_compl _ hS]
    refine add_le_add ?_ ?_
    · -- Hörmander part
      have := hCH K B hK1 ρ hρ0 z
      exact this.trans (add_le_add (hK2 z hz0) le_rfl)
    · -- the ball part
      have hpt : ∀ x ∈ Sᶜ, ‖J (x - z) - J x‖ₑ ≤
          (ball (0 : V) ρ).indicator (fun _ => ENNReal.ofReal (B / ρ ^ d)) x := by
        intro x hx
        have hx' : ‖x‖ < ρ := by
          simp only [S, mem_compl_iff, mem_setOf_eq, not_le, hznorm] at hx; linarith
        have hJx : J x = 0 := by
          simp only [hJ]; rw [indicator_of_notMem]; simp [hx']
        rw [hJx, sub_zero, indicator_of_mem (by rwa [mem_ball_zero_iff])]
        by_cases hxz : ρ ≤ ‖x - z‖
        · simp only [hJ]
          rw [indicator_of_mem (show x - z ∈ {x : V | ρ ≤ ‖x‖} from hxz),
            ← ofReal_norm_eq_enorm]
          have hxz0 : x - z ≠ 0 := by
            intro h; rw [h, norm_zero] at hxz; linarith
          refine ENNReal.ofReal_le_ofReal ((hK1 _ hxz0).trans ?_)
          exact div_le_div_of_nonneg_left hB (by positivity) (pow_le_pow_left₀ hρ0.le hxz _)
        · simp only [hJ]
          rw [indicator_of_notMem (show x - z ∉ {x : V | ρ ≤ ‖x‖} from hxz), enorm_zero]
          exact bot_le
      calc _ ≤ ∫⁻ x in Sᶜ, (ball (0 : V) ρ).indicator (fun _ => ENNReal.ofReal (B / ρ ^ d)) x :=
            setLIntegral_mono' hS.compl hpt
        _ ≤ ∫⁻ x, (ball (0 : V) ρ).indicator (fun _ => ENNReal.ofReal (B / ρ ^ d)) x :=
            setLIntegral_le_lintegral _ _
        _ = ENNReal.ofReal (B / ρ ^ d) * volume (ball (0 : V) ρ) :=
            lintegral_indicator_const measurableSet_ball _
        _ = ENNReal.ofReal (Vr * B) := by
            rw [Measure.addHaar_ball_of_pos _ _ hρ0, hfin]
            have hV : volume (ball (0 : V) 1) = ENNReal.ofReal Vr := by
              simp only [Vr, Measure.real]
              rw [ENNReal.ofReal_toReal measure_ball_lt_top.ne]
            rw [hV, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
              ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            field_simp
  -- combine
  have hI₂ : ‖∫ x, e x * J x‖ ≤ (B₁ + CH * B + Vr * B) / 2 := by
    have h3 : ‖∫ x, e x * (J x - J (x - z))‖ ≤ B₁ + CH * B + Vr * B := by
      have := hout
      rw [← ENNReal.ofReal_add hB₁ (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity), ← ofReal_norm_eq_enorm] at this
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 this
    rw [← h2, norm_mul] at h3
    have h22 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h22] at h3
    linarith
  rw [hF, ← hsplit, hcompl]
  calc ‖(∫ x in ball (0 : V) ρ, e x * K x) + ∫ x, e x * J x‖
      ≤ ‖∫ x in ball (0 : V) ρ, e x * K x‖ + ‖∫ x, e x * J x‖ := norm_add_le _ _
    _ ≤ 2 * π * d * Vr * B + (B₁ + CH * B + Vr * B) / 2 := add_le_add hI₁ hI₂
    _ ≤ (2 * π * d * Vr + CH + Vr + 1) * (B + B₁) := by
        have : 0 ≤ 2 * π * d * Vr := by positivity
        nlinarith [mul_nonneg this hB₁, mul_nonneg hCH0 hB₁, mul_nonneg hVr hB₁,
          mul_nonneg hCH0 hB, mul_nonneg hVr hB]

end DbarRegularity

open DbarRegularity

open MeasureTheory Set Metric FourierTransform
open scoped ENNReal Real RealInnerProductSpace

theorem solution {d : ℕ} (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (K : EuclideanSpace ℝ (Fin d) → ℂ) (B B₁ : ℝ), 0 ≤ B₁ →
      Integrable K volume →
      (∀ x, x ≠ 0 → ‖K x‖ ≤ B / ‖x‖ ^ d) →
      (∀ y, y ≠ 0 → ∫⁻ x in {x | 2 * ‖y‖ ≤ ‖x‖}, ‖K (x - y) - K x‖ₑ ≤ ENNReal.ofReal B₁) →
      (∀ r : ℝ, 0 < r → ∫ x in ball 0 r, K x = 0) →
      ∀ ξ, ‖𝓕 K ξ‖ ≤ C * (B + B₁) :=
  DbarRegularity.norm_fourier_le_of_hormander hd
