-- Prove2me | solution 1 for DiscServLine.SPT.corollary_1_attained
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T07:03:54.042168+00:00
-- url     : https://prove2.me/submissions/bd28fc1d-6c86-4b0c-8b4c-bbfe4573076d

import Mathlib
import Definitions.Def_DiscServLine_SPT_Model

open DiscServLine.SPT MeasureTheory Set

private lemma dens_meas (L : ℝ) : Measurable (fun t : ℝ => ENNReal.ofReal (L / t ^ 3)) := by
  fun_prop

private lemma setInt_cor (L H : ℝ) (hL : 0 < L) (s : Set ℝ) (hs : MeasurableSet s) (f : ℝ → ℝ) :
    ∫ x in s, f x ∂((volume.restrict (Icc L H)).withDensity (fun t => ENNReal.ofReal (L / t ^ 3)))
      = ∫ x in s ∩ Icc L H, (L / x ^ 3) * f x := by
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul' s (dens_meas L)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) f]
  rw [Measure.restrict_restrict' measurableSet_Icc]
  apply setIntegral_congr_fun (hs.inter measurableSet_Icc)
  intro x hx
  have hx0 : 0 < x := lt_of_lt_of_le hL hx.2.1
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (by positivity)]

private lemma ftc (a b : ℝ) (hab : a ≤ b) (ha : 0 < a) (G g : ℝ → ℝ)
    (hG : ∀ x, 0 < x → HasDerivAt G (g x) x) (hg : ContinuousOn g (Icc a b)) :
    ∫ x in Icc a b, g x = G b - G a := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx; rw [uIcc_of_le hab] at hx; exact hG x (by linarith [hx.1])
  · exact hg.intervalIntegrable_of_Icc hab

private lemma pos_near (L H : ℝ) (hL : 0 < L) (a b : ℝ) (hab : a < b) (S : Set ℝ)
    (hsub : Ioo a b ⊆ S ∩ Icc L H) (hpos : ∀ x ∈ Ioo a b, 0 < L / x ^ 3) :
    0 < ((volume.restrict (Icc L H)).withDensity (fun t => ENNReal.ofReal (L / t ^ 3))) S := by
  rw [pos_iff_ne_zero, Ne, withDensity_apply_eq_zero' (dens_meas L).aemeasurable,
    Measure.restrict_apply' measurableSet_Icc]
  intro h
  have h0 : volume (Ioo a b) = 0 := by
    apply measure_mono_null _ h
    intro x hx
    refine ⟨⟨?_, (hsub hx).1⟩, (hsub hx).2⟩
    simp only [mem_setOf_eq, Ne, ENNReal.ofReal_eq_zero, not_le]
    exact hpos x hx
  rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at h0
  linarith

theorem solution (Λ0 Λ1 : ℝ) (h0 : 0 < Λ0) (h1 : 0 < Λ1) (h1' : Λ1 < 1) :
    Admissible (cor1Design Λ0 Λ1) ∧ (cor1Design Λ0 Λ1).lo < (cor1Design Λ0 Λ1).hi ∧
      (cor1Design Λ0 Λ1).Λk 0 = Λ0 ∧ (cor1Design Λ0 Λ1).Λk 1 = Λ1 ∧
      (cor1Design Λ0 Λ1).Q = (1 / 2 : ℝ) * (Real.log (1 - Λ1)) ^ 2 := by
  set L := cor1Lo Λ0 Λ1 with hLdef
  set H := L / (1 - Λ1) with hHdef
  have hu : 0 < 1 - Λ1 := by linarith
  have hL2 : 2 * L * Λ0 = 1 - (1 - Λ1) ^ 2 := by
    rw [hLdef, cor1Lo]; field_simp
  have hL : 0 < L := by
    rw [hLdef, cor1Lo]; apply div_pos _ (by positivity); nlinarith
  have hLH : L < H := by
    rw [hHdef, lt_div_iff₀ hu]; nlinarith
  have hH : 0 < H := by linarith
  have hlo : (cor1Design Λ0 Λ1).lo = L := rfl
  have hhi : (cor1Design Λ0 Λ1).hi = H := rfl
  have hμ : (cor1Design Λ0 Λ1).μ =
      (volume.restrict (Icc L H)).withDensity (fun t => ENNReal.ofReal (L / t ^ 3)) := rfl
  have hint : ∀ f : ℝ → ℝ, ∫ x, f x ∂(cor1Design Λ0 Λ1).μ = ∫ x in Icc L H, (L / x ^ 3) * f x := by
    intro f
    have := setInt_cor L H hL univ MeasurableSet.univ f
    rw [Measure.restrict_univ, univ_inter] at this
    rw [hμ, this]
  have hcont : ∀ (g : ℝ → ℝ), Continuous g → ∀ a b, 0 < a →
      ContinuousOn (fun x => L / x ^ 3 * g x) (Icc a b) := by
    intro g hg a b ha
    apply ContinuousOn.mul _ hg.continuousOn
    exact continuousOn_const.div (continuousOn_pow 3) (fun x hx => by
      have : 0 < x := lt_of_lt_of_le ha hx.1
      positivity)
  have hlogHL : Real.log H - Real.log L = -Real.log (1 - Λ1) := by
    rw [← Real.log_div hH.ne' hL.ne', show H / L = (1 - Λ1)⁻¹ by rw [hHdef]; field_simp,
      Real.log_inv]
  -- moments
  have hΛ0 : (cor1Design Λ0 Λ1).Λk 0 = Λ0 := by
    unfold Design.Λk; rw [hint]
    rw [ftc L H hLH.le hL (fun x => -(L / 2) * (x ^ 2)⁻¹) (fun x => L / x ^ 3 * x ^ 0)
      (fun x hx => (((hasDerivAt_pow 2 x).inv (by positivity)).const_mul (-(L / 2))).congr_deriv
        (by field_simp; ring)) (hcont _ (continuous_pow 0) _ _ hL)]
    rw [hHdef]; field_simp; nlinarith
  have hΛ1 : (cor1Design Λ0 Λ1).Λk 1 = Λ1 := by
    unfold Design.Λk; rw [hint]
    rw [ftc L H hLH.le hL (fun x => -L * x⁻¹) (fun x => L / x ^ 3 * x ^ 1)
      (fun x hx => ((hasDerivAt_inv hx.ne').const_mul (-L)).congr_deriv
        (by field_simp)) (hcont _ (continuous_pow 1) _ _ hL)]
    rw [hHdef]; field_simp; ring
  have hΛ2 : (cor1Design Λ0 Λ1).Λk 2 = -L * Real.log (1 - Λ1) := by
    unfold Design.Λk; rw [hint]
    rw [ftc L H hLH.le hL (fun x => L * Real.log x) (fun x => L / x ^ 3 * x ^ 2)
      (fun x hx => ((Real.hasDerivAt_log hx.ne').const_mul L).congr_deriv
        (by field_simp)) (hcont _ (continuous_pow 2) _ _ hL)]
    rw [← mul_sub, hlogHL]; ring
  -- loads on the line
  have hload : ∀ t ∈ Icc L H, (cor1Design Λ0 Λ1).loadBelow t = 1 - L / t ∧
      (cor1Design Λ0 Λ1).loadUpTo t = 1 - L / t := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hL ht.1
    have hF : ∫ x in Icc L t, L / x ^ 3 * x = 1 - L / t := by
      rw [ftc L t ht.1 hL (fun x => -L * x⁻¹) (fun x => L / x ^ 3 * x)
        (fun x hx => ((hasDerivAt_inv hx.ne').const_mul (-L)).congr_deriv
          (by field_simp)) (hcont _ continuous_id _ _ hL)]
      field_simp; ring
    constructor
    · unfold Design.loadBelow
      rw [hμ, setInt_cor L H hL _ measurableSet_Iio]
      have : Iio t ∩ Icc L H = Ico L t := by
        ext x; simp only [mem_inter_iff, mem_Iio, mem_Icc, mem_Ico]
        constructor
        · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1⟩
        · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith [ht.2]⟩
      rw [this, ← integral_Icc_eq_integral_Ico, hF]
    · unfold Design.loadUpTo
      rw [hμ, setInt_cor L H hL _ measurableSet_Iic]
      have : Iic t ∩ Icc L H = Icc L t := by
        ext x; simp only [mem_inter_iff, mem_Iic, mem_Icc]
        constructor
        · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1⟩
        · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith [ht.2]⟩
      rw [this, hF]
  -- queue length
  have hQ : (cor1Design Λ0 Λ1).Q = (1 / 2 : ℝ) * (Real.log (1 - Λ1)) ^ 2 := by
    unfold Design.Q; rw [hint]
    have hcongr : ∫ x in Icc L H, L / x ^ 3 * (cor1Design Λ0 Λ1).W x =
        ∫ x in Icc L H, L / x ^ 3 * ((-L * Real.log (1 - Λ1)) / (2 * L ^ 2) * x ^ 2) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le hL hx.1
      simp only
      unfold Design.W
      rw [(hload x hx).1, (hload x hx).2, hΛ2]
      congr 1
      field_simp
      rw [show x - (x - L) = L by ring]
      field_simp
    rw [hcongr]
    rw [ftc L H hLH.le hL (fun x => (-Real.log (1 - Λ1)) / (2 * L) * L * Real.log x)
      (fun x => L / x ^ 3 * ((-L * Real.log (1 - Λ1)) / (2 * L ^ 2) * x ^ 2))
      (fun x hx => ((Real.hasDerivAt_log hx.ne').const_mul _).congr_deriv
        (by field_simp)) (hcont _ (continuous_pow 2 |>.const_mul _) _ _ hL)]
    rw [← mul_sub, hlogHL]; field_simp
  refine ⟨?_, hLH, hΛ0, hΛ1, hQ⟩
  -- admissibility
  refine ⟨?_, hL.le, hLH.le, ?_, ?_, ?_, by rw [hΛ1]; exact h1'⟩
  · rw [hμ]
    apply isFiniteMeasure_withDensity_ofReal
    have : IntegrableOn (fun x : ℝ => L / x ^ 3 * 1) (Icc L H) volume :=
      (hcont (fun _ => 1) continuous_const L H hL).integrableOn_Icc
    simp only [mul_one] at this
    exact this.hasFiniteIntegral
  · rw [hμ, withDensity_apply_eq_zero' (dens_meas L).aemeasurable,
      Measure.restrict_apply' measurableSet_Icc]
    apply measure_mono_null _ measure_empty
    intro x hx; exact absurd hx.2 hx.1.2
  · intro ε hε
    rw [hμ]
    apply pos_near L H hL L (min (L + ε) H) (lt_min (by linarith) hLH)
    · intro x hx
      exact ⟨⟨hx.1.le, lt_of_lt_of_le hx.2 (min_le_left _ _)⟩,
        ⟨hx.1.le, (lt_of_lt_of_le hx.2 (min_le_right _ _)).le⟩⟩
    · intro x hx; have : 0 < x := lt_trans hL hx.1; positivity
  · intro ε hε
    rw [hμ]
    apply pos_near L H hL (max (H - ε) L) H (max_lt (by linarith) hLH)
    · intro x hx
      exact ⟨⟨lt_of_le_of_lt (le_max_left _ _) hx.1, hx.2.le⟩,
        ⟨(lt_of_le_of_lt (le_max_right _ _) hx.1).le, hx.2.le⟩⟩
    · intro x hx; have : 0 < x := lt_of_le_of_lt (le_max_right _ _) hx.1 |> lt_trans hL; positivity
