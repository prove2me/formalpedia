-- Prove2me | solution 1 for DROReview.PhiDiv.lemma_5_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-19T18:14:49.407722+00:00
-- url     : https://prove2.me/submissions/52470634-49b3-4eae-a2f4-321ab3f5de24

import Mathlib
import Definitions.Def_DROReview_PhiDiv_phiDiv
import Definitions.Def_DROReview_PhiDiv_generators
import Definitions.Def_DROReview_PhiDiv_ball

set_option autoImplicit false

open MeasureTheory Filter Topology

namespace P13de

open DROReview.PhiDiv

lemma phiH_le_phiKL (t : NNReal) : phiH t ≤ phiKL t := by
  unfold phiH phiKL
  apply ENNReal.ofReal_le_ofReal
  have ht : (0:ℝ) ≤ t := t.2
  rcases eq_or_lt_of_le ht with h0 | hpos
  · rw [← h0]; simp
  · have hs0 : 0 < Real.sqrt (t:ℝ) := Real.sqrt_pos.2 hpos
    have hts : (t:ℝ) = (Real.sqrt (t:ℝ))^2 := (Real.sq_sqrt ht).symm
    have hlog : Real.log (t:ℝ) = 2 * Real.log (Real.sqrt (t:ℝ)) := by
      conv_lhs => rw [hts]
      rw [Real.log_pow]; push_cast; ring
    generalize Real.sqrt (t:ℝ) = s at *
    have h1 := Real.one_sub_inv_le_log_of_pos hs0
    have h2 : s - 1 ≤ s * Real.log s := by
      have := mul_le_mul_of_nonneg_left h1 hs0.le
      rwa [mul_sub, mul_one, mul_inv_cancel₀ hs0.ne'] at this
    rw [hlog, hts]
    nlinarith [mul_le_mul_of_nonneg_left h2 hs0.le]

lemma phiKL_le_phiJ (t : NNReal) : phiKL t ≤ phiJ t := by
  unfold phiKL phiJ
  split_ifs with h
  · exact le_top
  · apply ENNReal.ofReal_le_ofReal
    have hpos : (0:ℝ) < t := NNReal.coe_pos.2 (pos_iff_ne_zero.2 h)
    have := Real.log_le_sub_one_of_pos hpos
    nlinarith

lemma slope_mono {φ ψ : NNReal → ENNReal} (h : ∀ t, φ t ≤ ψ t) :
    phiSlope φ ≤ phiSlope ψ := by
  unfold phiSlope
  exact limsup_le_limsup (Eventually.of_forall fun t => ENNReal.div_le_div_right (h t) _)

lemma slopeV_le : phiSlope phiV ≤ 1 := by
  unfold phiSlope
  refine limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [eventually_ge_atTop (1:NNReal)] with t ht
  apply ENNReal.div_le_of_le_mul
  rw [one_mul]
  unfold phiV
  have h1 : (1:ℝ) ≤ t := by exact_mod_cast ht
  have : |(t:ℝ) - 1| ≤ t := by
    rw [abs_of_nonneg (by linarith)]; linarith
  calc ENNReal.ofReal |(t:ℝ)-1| ≤ ENNReal.ofReal t := ENNReal.ofReal_le_ofReal this
    _ = (t:ENNReal) := ENNReal.ofReal_coe_nnreal

lemma one_le_slopeH : 1 ≤ phiSlope phiH := by
  unfold phiSlope
  have hT : Tendsto (fun t : NNReal => phiH t / (t:ENNReal)) atTop (𝓝 1) := by
    have hr : Tendsto (fun t : NNReal => (1 - (Real.sqrt (t:ℝ))⁻¹)^2) atTop
        (𝓝 ((1 - 0)^2)) := by
      have h1 : Tendsto (fun t : NNReal => (t:ℝ)) atTop atTop :=
        NNReal.tendsto_coe_atTop.2 tendsto_id
      have h2 := tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp h1)
      exact (tendsto_const_nhds.sub h2).pow 2
    have hr' := ENNReal.tendsto_ofReal hr
    simp only [sub_zero, one_pow, ENNReal.ofReal_one] at hr'
    refine hr'.congr' ?_
    filter_upwards [eventually_gt_atTop (0:NNReal)] with t ht
    unfold phiH
    have htr : (0:ℝ) < t := ht
    rw [show (t:ENNReal) = ENNReal.ofReal t from (ENNReal.ofReal_coe_nnreal).symm,
        ← ENNReal.ofReal_div_of_pos htr]
    congr 1
    have hs := Real.sqrt_pos.2 htr
    have hsq := Real.sq_sqrt htr.le
    generalize Real.sqrt (t:ℝ) = s at *
    rw [eq_div_iff htr.ne', ← hsq]
    field_simp
  rw [hT.limsup_eq]

lemma V_pt (a b : NNReal) :
    (if (b:ENNReal) = 0 then (a:ENNReal) * phiSlope phiV
      else (b:ENNReal) * phiV ((a:ENNReal) / b).toNNReal)
      ≤ ENNReal.ofReal |(a:ℝ) - b| := by
  split_ifs with h
  · have hb : b = 0 := by exact_mod_cast h
    subst hb
    calc (a:ENNReal) * phiSlope phiV ≤ (a:ENNReal) * 1 := mul_le_mul' le_rfl slopeV_le
      _ = ENNReal.ofReal |(a:ℝ) - ((0:NNReal):ℝ)| := by simp
  · have hb : b ≠ 0 := by intro h'; apply h; simp [h']
    rw [← ENNReal.coe_div hb, ENNReal.toNNReal_coe]
    unfold phiV
    rw [← ENNReal.ofReal_coe_nnreal (p := b), ← ENNReal.ofReal_mul (NNReal.coe_nonneg b)]
    apply le_of_eq; congr 1
    have hbr : (0:ℝ) < b := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hb)
    have e : (a:ℝ) - b = b * (a / b - 1) := by field_simp
    rw [NNReal.coe_div, e, abs_mul, abs_of_pos hbr]

lemma H_pt (a b : NNReal) :
    ENNReal.ofReal ((Real.sqrt a - Real.sqrt b)^2) ≤
    (if (b:ENNReal) = 0 then (a:ENNReal) * phiSlope phiH
      else (b:ENNReal) * phiH ((a:ENNReal) / b).toNNReal) := by
  split_ifs with h
  · have hb : b = 0 := by exact_mod_cast h
    subst hb
    calc ENNReal.ofReal ((Real.sqrt a - Real.sqrt ((0:NNReal):ℝ))^2) = (a:ENNReal) * 1 := by
          simp
      _ ≤ _ := mul_le_mul' le_rfl one_le_slopeH
  · have hb : b ≠ 0 := by intro h'; apply h; simp [h']
    rw [← ENNReal.coe_div hb, ENNReal.toNNReal_coe]
    unfold phiH
    rw [← ENNReal.ofReal_coe_nnreal (p := b), ← ENNReal.ofReal_mul (NNReal.coe_nonneg b)]
    apply le_of_eq; congr 1
    have hbr : (0:ℝ) < b := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hb)
    have hsb0 : 0 < Real.sqrt (b:ℝ) := Real.sqrt_pos.2 hbr
    have hsb : Real.sqrt (b:ℝ) ^ 2 = b := Real.sq_sqrt hbr.le
    rw [NNReal.coe_div, Real.sqrt_div' _ hbr.le]
    symm
    calc (b:ℝ) * (Real.sqrt a / Real.sqrt b - 1) ^ 2
        = (Real.sqrt b) ^ 2 * (Real.sqrt a / Real.sqrt b - 1) ^ 2 := by rw [hsb]
      _ = (Real.sqrt a - Real.sqrt b) ^ 2 := by field_simp

lemma sq_rpow_half (X : ENNReal) : (X ^ (1/2:ℝ)) ^ 2 = X := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num

lemma cs_part {α : Type*} [MeasurableSpace α] (ν : Measure α) (p q : α → ENNReal)
    (hp : Measurable p) (hq : Measurable q) (hp1 : ∫⁻ x, p x ∂ν ≤ 1)
    (hq1 : ∫⁻ x, q x ∂ν ≤ 1) :
    (∫⁻ x, ENNReal.ofReal |((p x).toNNReal:ℝ) - (q x).toNNReal| ∂ν) ^ 2 ≤
      4 * ∫⁻ x, ENNReal.ofReal ((Real.sqrt ((p x).toNNReal) - Real.sqrt ((q x).toNNReal))^2)
        ∂ν := by
  set A : α → ℝ := fun x => Real.sqrt ((p x).toNNReal) with hAdef
  set B : α → ℝ := fun x => Real.sqrt ((q x).toNNReal) with hBdef
  have hA : Measurable A := by
    simp only [hAdef]; exact hp.ennreal_toNNReal.coe_nnreal_real.sqrt
  have hB : Measurable B := by
    simp only [hBdef]; exact hq.ennreal_toNNReal.coe_nnreal_real.sqrt
  set f : α → ENNReal := fun x => ENNReal.ofReal |A x - B x| with hfdef
  set g : α → ENNReal := fun x => ENNReal.ofReal (A x + B x) with hgdef
  have hf : Measurable f := ((hA.sub hB).abs).ennreal_ofReal
  have hg : Measurable g := (hA.add hB).ennreal_ofReal
  have hfg : ∀ x, ENNReal.ofReal |((p x).toNNReal:ℝ) - (q x).toNNReal| = (f * g) x := by
    intro x
    simp only [Pi.mul_apply, hfdef, hgdef]
    rw [← ENNReal.ofReal_mul (abs_nonneg _)]
    congr 1
    have hA2 : A x ^ 2 = (p x).toNNReal := Real.sq_sqrt (NNReal.coe_nonneg _)
    have hB2 : B x ^ 2 = (q x).toNNReal := Real.sq_sqrt (NNReal.coe_nonneg _)
    have hAB : 0 ≤ A x + B x := add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    rw [← hA2, ← hB2, show A x ^ 2 - B x ^ 2 = (A x - B x) * (A x + B x) by ring, abs_mul,
      abs_of_nonneg hAB]
  have hf2 : ∀ x, f x ^ (2:ℝ) =
      ENNReal.ofReal ((Real.sqrt ((p x).toNNReal) - Real.sqrt ((q x).toNNReal))^2) := by
    intro x
    simp only [hfdef]
    rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  have hg2 : ∀ x, g x ^ (2:ℝ) ≤ 2 * p x + 2 * q x := by
    intro x
    simp only [hgdef]
    rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (add_nonneg (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _))]
    have hA2 : A x ^ 2 = (p x).toNNReal := Real.sq_sqrt (NNReal.coe_nonneg _)
    have hB2 : B x ^ 2 = (q x).toNNReal := Real.sq_sqrt (NNReal.coe_nonneg _)
    have h1 : (A x + B x) ^ 2 ≤ 2 * ((p x).toNNReal : ℝ) + 2 * ((q x).toNNReal : ℝ) := by
      rw [← hA2, ← hB2]; nlinarith [sq_nonneg (A x - B x)]
    calc ENNReal.ofReal ((A x + B x) ^ 2)
        ≤ ENNReal.ofReal (2 * ((p x).toNNReal : ℝ) + 2 * ((q x).toNNReal : ℝ)) :=
          ENNReal.ofReal_le_ofReal h1
      _ = 2 * ((p x).toNNReal : ENNReal) + 2 * ((q x).toNNReal : ENNReal) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
          simp
      _ ≤ 2 * p x + 2 * q x := by
          gcongr <;> exact ENNReal.coe_toNNReal_le_self
  have hY : ∫⁻ x, g x ^ (2:ℝ) ∂ν ≤ 4 := by
    calc ∫⁻ x, g x ^ (2:ℝ) ∂ν ≤ ∫⁻ x, (2 * p x + 2 * q x) ∂ν := lintegral_mono hg2
      _ = 2 * ∫⁻ x, p x ∂ν + 2 * ∫⁻ x, q x ∂ν := by
          rw [lintegral_add_left (hp.const_mul 2), lintegral_const_mul _ hp,
            lintegral_const_mul _ hq]
      _ ≤ 2 * 1 + 2 * 1 := by gcongr
      _ = 4 := by norm_num
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two
    hf.aemeasurable hg.aemeasurable
  simp only [hf2] at hH
  rw [lintegral_congr hfg]
  calc (∫⁻ x, (f * g) x ∂ν) ^ 2
      ≤ ((∫⁻ x, ENNReal.ofReal ((Real.sqrt ((p x).toNNReal) -
          Real.sqrt ((q x).toNNReal))^2) ∂ν) ^ (1/2:ℝ) *
          (∫⁻ x, g x ^ (2:ℝ) ∂ν) ^ (1/2:ℝ)) ^ 2 := by gcongr
    _ = (∫⁻ x, ENNReal.ofReal ((Real.sqrt ((p x).toNNReal) -
          Real.sqrt ((q x).toNNReal))^2) ∂ν) * ∫⁻ x, g x ^ (2:ℝ) ∂ν := by
          rw [mul_pow, sq_rpow_half, sq_rpow_half]
    _ ≤ (∫⁻ x, ENNReal.ofReal ((Real.sqrt ((p x).toNNReal) -
          Real.sqrt ((q x).toNNReal))^2) ∂ν) * 4 := by gcongr
    _ = _ := mul_comm _ _

lemma key {α : Type*} [MeasurableSpace α] (ν : Measure α) (p q : α → ENNReal)
    (hp : Measurable p) (hq : Measurable q) (hp1 : ∫⁻ x, p x ∂ν ≤ 1)
    (hq1 : ∫⁻ x, q x ∂ν ≤ 1) (hpt : ∀ᵐ x ∂ν, p x ≠ ⊤) (hqt : ∀ᵐ x ∂ν, q x ≠ ⊤) :
    (∫⁻ x, (if q x = 0 then p x * phiSlope phiV
      else q x * phiV (p x / q x).toNNReal) ∂ν) ^ 2 ≤
    4 * ∫⁻ x, (if q x = 0 then p x * phiSlope phiH
      else q x * phiH (p x / q x).toNNReal) ∂ν := by
  have hV : ∫⁻ x, (if q x = 0 then p x * phiSlope phiV
      else q x * phiV (p x / q x).toNNReal) ∂ν ≤
      ∫⁻ x, ENNReal.ofReal |((p x).toNNReal:ℝ) - (q x).toNNReal| ∂ν := by
    apply lintegral_mono_ae
    filter_upwards [hpt, hqt] with x hx1 hx2
    have := V_pt (p x).toNNReal (q x).toNNReal
    rwa [ENNReal.coe_toNNReal hx1, ENNReal.coe_toNNReal hx2] at this
  have hH : ∫⁻ x, ENNReal.ofReal ((Real.sqrt ((p x).toNNReal) -
      Real.sqrt ((q x).toNNReal))^2) ∂ν ≤
      ∫⁻ x, (if q x = 0 then p x * phiSlope phiH
        else q x * phiH (p x / q x).toNNReal) ∂ν := by
    apply lintegral_mono_ae
    filter_upwards [hpt, hqt] with x hx1 hx2
    have := H_pt (p x).toNNReal (q x).toNNReal
    rwa [ENNReal.coe_toNNReal hx1, ENNReal.coe_toNNReal hx2] at this
  calc _ ≤ (∫⁻ x, ENNReal.ofReal |((p x).toNNReal:ℝ) - (q x).toNNReal| ∂ν) ^ 2 := by
        gcongr
    _ ≤ 4 * ∫⁻ x, ENNReal.ofReal ((Real.sqrt ((p x).toNNReal) -
          Real.sqrt ((q x).toNNReal))^2) ∂ν := cs_part ν p q hp hq hp1 hq1
    _ ≤ _ := by gcongr

lemma vh {Ξ : Type*} [MeasurableSpace Ξ] (P P₀ : ProbabilityMeasure Ξ) :
    (phiDiv phiV P P₀) ^ 2 ≤ 4 * phiDiv phiH P P₀ := by
  unfold phiDiv
  dsimp only
  exact key _ _ _ (Measure.measurable_rnDeriv _ _) (Measure.measurable_rnDeriv _ _)
    (Measure.lintegral_rnDeriv_le.trans prob_le_one)
    (Measure.lintegral_rnDeriv_le.trans prob_le_one)
    ((Measure.rnDeriv_lt_top _ _).mono fun x hx => hx.ne)
    ((Measure.rnDeriv_lt_top _ _).mono fun x hx => hx.ne)

lemma div_mono {Ξ : Type*} [MeasurableSpace Ξ] {φ ψ : NNReal → ENNReal}
    (h : ∀ t, φ t ≤ ψ t) (P P₀ : ProbabilityMeasure Ξ) :
    phiDiv φ P P₀ ≤ phiDiv ψ P P₀ := by
  unfold phiDiv
  dsimp only
  apply lintegral_mono
  intro x
  dsimp only
  split_ifs
  · exact mul_le_mul' le_rfl (slope_mono h)
  · exact mul_le_mul' le_rfl (h _)

lemma v_le {Ξ : Type*} [MeasurableSpace Ξ] (P P₀ : ProbabilityMeasure Ξ) (ε : ENNReal)
    (hP : phiDiv phiH P P₀ ≤ ε) : phiDiv phiV P P₀ ≤ 2 * ε ^ (1 / (2 : ℝ)) := by
  have h1 : (phiDiv phiV P P₀) ^ 2 ≤ 2 ^ 2 * ε := by
    calc _ ≤ 4 * phiDiv phiH P P₀ := vh P P₀
      _ ≤ 4 * ε := by gcongr
      _ = 2 ^ 2 * ε := by norm_num
  have h2 := ENNReal.rpow_le_rpow h1 (show (0:ℝ) ≤ 1/2 by norm_num)
  have e1 : ∀ X : ENNReal, (X ^ 2) ^ (1/2:ℝ) = X := by
    intro X; rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), e1, e1] at h2
  simpa using h2

end P13de

open MeasureTheory DROReview.PhiDiv in
theorem solution {Ξ : Type*} [MeasurableSpace Ξ]
    (P P₀ : ProbabilityMeasure Ξ) (ε : ENNReal) :
    ((1 / 4 : ENNReal) *
        (phiDiv phiV P P₀) ^ 2 ≤
        phiDiv phiH P P₀) ∧
    (phiDiv phiH P P₀ ≤
      phiDiv phiKL P P₀) ∧
    (phiDiv phiKL P P₀ ≤
      phiDiv phiJ P P₀) ∧
    (phiBall phiJ P₀ ε ⊆ phiBall phiKL P₀ ε) ∧
    (phiBall phiKL P₀ ε ⊆ phiBall phiH P₀ ε) ∧
    (phiBall phiH P₀ ε ⊆ phiBall phiV P₀
      (2 * ε ^ (1 / (2 : ℝ)))) := by
  refine ⟨?_, P13de.div_mono P13de.phiH_le_phiKL P P₀, P13de.div_mono P13de.phiKL_le_phiJ P P₀, ?_, ?_, ?_⟩
  · calc (1 / 4 : ENNReal) * (phiDiv phiV P P₀) ^ 2
        ≤ (1 / 4 : ENNReal) * (4 * phiDiv phiH P P₀) := by gcongr; exact P13de.vh P P₀
      _ = phiDiv phiH P P₀ := by
        rw [← mul_assoc, ENNReal.div_mul_cancel (by norm_num) (by norm_num), one_mul]
  · intro Q hQ
    exact (P13de.div_mono P13de.phiKL_le_phiJ Q P₀).trans hQ
  · intro Q hQ
    exact (P13de.div_mono P13de.phiH_le_phiKL Q P₀).trans hQ
  · intro Q hQ
    exact P13de.v_le Q P₀ ε hQ
