-- Prove2me | solution 1 for DbarRegularity.hormander_div_norm_pow_of_dini
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T19:42:15.884261+00:00
-- url     : https://prove2.me/submissions/59ddda30-bcc1-4b10-82f8-a6df86796dd4

import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Theorems.Thm_DbarRegularity_lintegral_fun_norm_eq
import Theorems.Thm_DbarRegularity_abs_inv_pow_sub_inv_pow_le
import Theorems.Thm_DbarRegularity_norm_inv_norm_smul_sub_le
import Theorems.Thm_DbarRegularity_lintegral_Ici_comp_div_mul_inv
import Theorems.Thm_DbarRegularity_lintegral_inv_norm_pow_succ_le



namespace DbarRegularity

open MeasureTheory Set Metric
open scoped ENNReal

/-- Let `Ω` on `ℝ^d` (`d ≥ 1`) be homogeneous of degree `0`, bounded by `M`, with spherical modulus of
continuity `w` satisfying `∫₀¹ w(δ) / δ dδ < ∞`. Then the kernel `K(x) = Ω(x) / |x|^d` satisfies
`∫_{|x| ≥ 2|y|} |K(x - y) - K(x)| dx ≤ H` for all `y ≠ 0`, with `H` independent of `y`. -/
theorem hormander_div_norm_pow_of_dini {d : ℕ} (hd : 0 < d) (Ω : EuclideanSpace ℝ (Fin d) → ℂ)
    (hhom : ∀ x, ∀ t : ℝ, 0 < t → Ω (t • x) = Ω x)
    (hdini : ∫⁻ δ in Set.Ioc (0 : ℝ) 1,
      (⨆ (x : EuclideanSpace ℝ (Fin d)) (x' : EuclideanSpace ℝ (Fin d)) (_ : ‖x‖ = 1)
        (_ : ‖x'‖ = 1) (_ : ‖x - x'‖ ≤ δ), ‖Ω x - Ω x'‖ₑ) / ENNReal.ofReal δ < ⊤)
    (M : ℝ) (hM : ∀ x, ‖Ω x‖ ≤ M) :
    ∃ H : ℝ, ∀ y : EuclideanSpace ℝ (Fin d), y ≠ 0 →
      ∫⁻ x in {x | 2 * ‖y‖ ≤ ‖x‖},
        ‖Ω (x - y) / ((‖x - y‖ ^ d : ℝ) : ℂ) - Ω x / ((‖x‖ ^ d : ℝ) : ℂ)‖ₑ
        ≤ ENNReal.ofReal H := by
  set W : ℝ → ℝ≥0∞ := fun δ => ⨆ (x : EuclideanSpace ℝ (Fin d)) (x' : EuclideanSpace ℝ (Fin d))
    (_ : ‖x‖ = 1) (_ : ‖x'‖ = 1) (_ : ‖x - x'‖ ≤ δ), ‖Ω x - Ω x'‖ₑ with hW
  set D : ℝ≥0∞ := ∫⁻ δ in Set.Ioc (0 : ℝ) 1, W δ / ENNReal.ofReal δ with hD
  have hDfin : D ≠ ⊤ := hdini.ne
  have hWmono : Monotone W := by
    intro δ δ' h
    exact iSup_mono fun x => iSup_mono fun x' => iSup_mono fun _ => iSup_mono fun _ =>
      iSup_mono' fun h1 => ⟨h1.trans h, le_rfl⟩
  have hWm : Measurable W := hWmono.measurable
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  obtain ⟨C₀, hC₀⟩ := lintegral_inv_norm_pow_succ_le d
  set κ : ℝ := 2 * d * 3 ^ (d - 1) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  set c1 : ℝ≥0∞ := d * volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1) *
    (ENNReal.ofReal (2 ^ d) * D) with hc1
  have hc1fin : c1 ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top d)
      measure_ball_lt_top.ne) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hDfin)
  refine ⟨c1.toReal + max 0 (M * κ * C₀ / 2), fun y hy => ?_⟩
  set a : ℝ := ‖y‖ with ha
  have ha0 : 0 < a := norm_pos_iff.mpr hy
  set S : Set (EuclideanSpace ℝ (Fin d)) := {x | 2 * a ≤ ‖x‖} with hS
  have hSm : MeasurableSet S := measurableSet_le measurable_const measurable_norm
  set G1 : EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := fun x =>
    W (2 * a / ‖x‖) * ENNReal.ofReal (2 ^ d / ‖x‖ ^ d) with hG1
  set G2 : EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (M * κ * a) * ENNReal.ofReal ((‖x‖ ^ (d + 1))⁻¹) with hG2
  have hG1m : Measurable G1 := by
    refine (hWm.comp ?_).mul ?_
    · exact measurable_const.div measurable_norm
    · exact ENNReal.measurable_ofReal.comp (measurable_const.div (measurable_norm.pow_const d))
  -- the radial projection
  set n : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun x => ‖x‖⁻¹ • x with hn
  have hnorm : ∀ x : EuclideanSpace ℝ (Fin d), x ≠ 0 → ‖n x‖ = 1 := by
    intro x hx
    simp only [hn, norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)
  have hΩn : ∀ x : EuclideanSpace ℝ (Fin d), x ≠ 0 → Ω (n x) = Ω x := fun x hx =>
    hhom x _ (inv_pos.mpr (norm_pos_iff.mpr hx))
  -- pointwise bound
  have hpt : ∀ x ∈ S, ‖Ω (x - y) / ((‖x - y‖ ^ d : ℝ) : ℂ) - Ω x / ((‖x‖ ^ d : ℝ) : ℂ)‖ₑ ≤
      G1 x + G2 x := by
    intro x hx
    have hx2 : 2 * a ≤ ‖x‖ := hx
    have hc0 : 0 < ‖x‖ := by linarith
    have hx0 : x ≠ 0 := norm_pos_iff.mp hc0
    have hbc : |‖x - y‖ - ‖x‖| ≤ a := by
      have := abs_norm_sub_norm_le (x - y) x
      simpa [ha] using this
    have hb1 : ‖x‖ / 2 ≤ ‖x - y‖ := by have := neg_abs_le (‖x - y‖ - ‖x‖); linarith
    have hb0 : 0 < ‖x - y‖ := by linarith
    have hxy0 : x - y ≠ 0 := norm_pos_iff.mp hb0
    have hsplit : Ω (x - y) / ((‖x - y‖ ^ d : ℝ) : ℂ) - Ω x / ((‖x‖ ^ d : ℝ) : ℂ) =
        (Ω (x - y) - Ω x) * (((‖x - y‖ ^ d : ℝ) : ℂ))⁻¹ +
          Ω x * ((((‖x - y‖ ^ d : ℝ) : ℂ))⁻¹ - (((‖x‖ ^ d : ℝ) : ℂ))⁻¹) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]; ring
    rw [hsplit]
    refine (enorm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [enorm_mul]
      refine mul_le_mul' ?_ ?_
      · -- modulus of continuity
        rw [← hΩn (x - y) hxy0, ← hΩn x hx0]
        refine le_iSup_of_le (n (x - y)) (le_iSup_of_le (n x) (le_iSup_of_le (hnorm _ hxy0)
          (le_iSup_of_le (hnorm x hx0) (le_iSup_of_le ?_ le_rfl))))
        have := norm_inv_norm_smul_sub_le (x - y) x hx0
        simpa [hn, ha] using this
      · rw [← ofReal_norm, norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (pow_pos hb0 d)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [inv_le_iff_one_le_mul₀ (pow_pos hb0 d)]
        calc (1 : ℝ) = (‖x‖ / 2) ^ d * (2 ^ d / ‖x‖ ^ d) := by rw [div_pow]; field_simp
          _ ≤ ‖x - y‖ ^ d * (2 ^ d / ‖x‖ ^ d) := by gcongr
          _ = 2 ^ d / ‖x‖ ^ d * ‖x - y‖ ^ d := mul_comm _ _
    · show _ ≤ ENNReal.ofReal (M * κ * a) * ENNReal.ofReal ((‖x‖ ^ (d + 1))⁻¹)
      rw [enorm_mul]
      calc ‖Ω x‖ₑ * ‖(((‖x - y‖ ^ d : ℝ) : ℂ))⁻¹ - (((‖x‖ ^ d : ℝ) : ℂ))⁻¹‖ₑ
          ≤ ENNReal.ofReal M * ENNReal.ofReal (κ * a / ‖x‖ ^ (d + 1)) := by
            refine mul_le_mul' ?_ ?_
            · rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hM x)
            · rw [← ofReal_norm]
              refine ENNReal.ofReal_le_ofReal ?_
              rw [← Complex.ofReal_inv, ← Complex.ofReal_inv, ← Complex.ofReal_sub,
                Complex.norm_real, Real.norm_eq_abs]
              exact abs_inv_pow_sub_inv_pow_le d ha0 hx2 hbc
        _ = ENNReal.ofReal (M * κ * a) * ENNReal.ofReal ((‖x‖ ^ (d + 1))⁻¹) := by
            rw [← ENNReal.ofReal_mul hM0, ← ENNReal.ofReal_mul (by positivity)]
            congr 1; ring
  -- integrate
  have hI1 : ∫⁻ x in S, G1 x ≤ c1 := by
    set F1 : ℝ → ℝ≥0∞ := (Ici (2 * a)).indicator fun r =>
      W (2 * a / r) * ENNReal.ofReal (2 ^ d / r ^ d) with hF1
    have hF1m : Measurable F1 := by
      refine Measurable.indicator ((hWm.comp (measurable_const.div measurable_id)).mul ?_)
        measurableSet_Ici
      exact ENNReal.measurable_ofReal.comp (measurable_const.div (measurable_id.pow_const d))
    have h1 : ∫⁻ x in S, G1 x = ∫⁻ x : EuclideanSpace ℝ (Fin d), F1 ‖x‖ := by
      rw [← lintegral_indicator hSm]
      congr 1
    rw [h1, lintegral_fun_norm_eq hd F1 hF1m, hc1]
    refine mul_le_mul' le_rfl ?_
    calc ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (d - 1)) * F1 r
        = ∫⁻ r in Ioi (0 : ℝ), (Ici (2 * a)).indicator
            (fun r => ENNReal.ofReal (2 ^ d) * (W (2 * a / r) * (ENNReal.ofReal r)⁻¹)) r := by
          refine setLIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
          have hr0 : 0 < r := hr
          simp only [hF1, indicator]
          split_ifs
          · rw [← ENNReal.ofReal_inv_of_pos hr0]
            rw [mul_comm (W _), ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
              mul_comm (W _), ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
            congr 2
            obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
            simp only [Nat.add_sub_cancel]
            field_simp
            ring
          · simp
      _ ≤ ∫⁻ r, (Ici (2 * a)).indicator
            (fun r => ENNReal.ofReal (2 ^ d) * (W (2 * a / r) * (ENNReal.ofReal r)⁻¹)) r :=
          setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal (2 ^ d) * D := by
          rw [lintegral_indicator measurableSet_Ici, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_Ici_comp_div_mul_inv (by positivity) W, hD]
          simp only [div_eq_mul_inv]
  have hI2 : ∫⁻ x in S, G2 x ≤ ENNReal.ofReal (M * κ * C₀ / 2) := by
    rw [hG2, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ENNReal.ofReal (M * κ * a) * ∫⁻ x in S, ENNReal.ofReal ((‖x‖ ^ (d + 1))⁻¹)
        ≤ ENNReal.ofReal (M * κ * a) * ENNReal.ofReal (C₀ / (2 * a)) :=
          mul_le_mul' le_rfl (hC₀ (2 * a) (by positivity))
      _ = ENNReal.ofReal (M * κ * C₀ / 2) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1; field_simp
  calc ∫⁻ x in S, ‖Ω (x - y) / ((‖x - y‖ ^ d : ℝ) : ℂ) - Ω x / ((‖x‖ ^ d : ℝ) : ℂ)‖ₑ
      ≤ ∫⁻ x in S, (G1 x + G2 x) := setLIntegral_mono' hSm hpt
    _ = (∫⁻ x in S, G1 x) + ∫⁻ x in S, G2 x := lintegral_add_left hG1m _
    _ ≤ c1 + ENNReal.ofReal (max 0 (M * κ * C₀ / 2)) :=
        add_le_add hI1 (hI2.trans (ENNReal.ofReal_le_ofReal (le_max_right _ _)))
    _ = ENNReal.ofReal (c1.toReal + max 0 (M * κ * C₀ / 2)) := by
        rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (le_max_left _ _),
          ENNReal.ofReal_toReal hc1fin]

end DbarRegularity

open DbarRegularity

open MeasureTheory Set Metric
open scoped ENNReal

theorem solution {d : ℕ} (hd : 0 < d) (Ω : EuclideanSpace ℝ (Fin d) → ℂ)
    (hhom : ∀ x, ∀ t : ℝ, 0 < t → Ω (t • x) = Ω x)
    (hdini : ∫⁻ δ in Set.Ioc (0 : ℝ) 1,
      (⨆ (x : EuclideanSpace ℝ (Fin d)) (x' : EuclideanSpace ℝ (Fin d)) (_ : ‖x‖ = 1)
        (_ : ‖x'‖ = 1) (_ : ‖x - x'‖ ≤ δ), ‖Ω x - Ω x'‖ₑ) / ENNReal.ofReal δ < ⊤)
    (M : ℝ) (hM : ∀ x, ‖Ω x‖ ≤ M) :
    ∃ H : ℝ, ∀ y : EuclideanSpace ℝ (Fin d), y ≠ 0 →
      ∫⁻ x in {x | 2 * ‖y‖ ≤ ‖x‖},
        ‖Ω (x - y) / ((‖x - y‖ ^ d : ℝ) : ℂ) - Ω x / ((‖x‖ ^ d : ℝ) : ℂ)‖ₑ
        ≤ ENNReal.ofReal H :=
  hormander_div_norm_pow_of_dini hd Ω hhom hdini M hM
