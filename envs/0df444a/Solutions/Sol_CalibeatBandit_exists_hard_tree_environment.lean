-- Prove2me | solution 1 for CalibeatBandit.exists_hard_tree_environment
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T17:43:08.076204+00:00
-- url     : https://prove2.me/submissions/389aabb5-fdf0-4fc7-9733-39570ca6e282

import Mathlib
import Definitions.Def_CalibeatBandit_lower_bound_models
import Definitions.Def_CalibeatBandit_IsColStochastic
import Definitions.Def_CalibeatBandit_fixedPointSol
import Definitions.Def_CalibeatBandit_calibeatPolicy
import Definitions.Def_CalibeatBandit_pseudoSwapRegret
import Definitions.Def_CalibeatBandit_swapRegret
import Definitions.Def_CalibeatBandit_hard_tree_environment

section

set_option autoImplicit false

open Filter MeasureTheory Set InformationTheory
open scoped Interval ENNReal

namespace CalibeatBandit

def bonusTransform (η z : ℝ) : ℝ := z + η * z * (1 - z)

theorem bonusTransform_deriv (η z : ℝ) :
    HasDerivAt (bonusTransform η) (1 + η * (1 - 2 * z)) z := by
  unfold bonusTransform
  have h := (hasDerivAt_id z).add
    (((hasDerivAt_id z).const_mul η).mul ((hasDerivAt_const z (1 : ℝ)).sub (hasDerivAt_id z)))
  change HasDerivAt (fun x : ℝ => x + η * x * (1 - x)) _ z at h
  convert h using 1
  simp only [Pi.sub_apply, id_eq]
  ring

theorem bonusTransform_deriv_pos {η z : ℝ} (hη₀ : 0 ≤ η) (hη₁ : η < 1)
    (hz : z ∈ Icc (0 : ℝ) 1) : 0 < 1 + η * (1 - 2 * z) := by
  nlinarith [mul_nonneg hη₀ (sub_nonneg.mpr hz.2)]

theorem bonusTransform_strictMonoOn {η : ℝ} (hη₀ : 0 ≤ η) (hη₁ : η < 1) :
    StrictMonoOn (bonusTransform η) (Icc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  have h : 0 < 1 + η * (1 - x - y) := by
    nlinarith [mul_nonneg hη₀ (sub_nonneg.mpr hx.2), mul_nonneg hη₀ (sub_nonneg.mpr hy.2)]
  calc
    bonusTransform η x < bonusTransform η x + (y - x) * (1 + η * (1 - x - y)) :=
      lt_add_of_pos_right _ (mul_pos (sub_pos.mpr hxy) h)
    _ = bonusTransform η y := by unfold bonusTransform; ring

/-- The integral inequality after the change of variables in Appendix D.2.
The derivative is positive throughout the integration interval. -/
theorem bonus_log_jacobian_integral_le {η : ℝ} (hη₀ : 0 ≤ η) (hη₁ : η < 1) :
    (∫ z in (0 : ℝ)..1, (1 + η * (1 - 2 * z)) * Real.log (1 + η * (1 - 2 * z)))
      ≤ η ^ 2 / 3 := by
  let J (z : ℝ) := 1 + η * (1 - 2 * z)
  let F (z : ℝ) := J z * Real.log (J z)
  let G (z : ℝ) := (η + η ^ 2) + (-(2 * η) - 4 * η ^ 2) * z + (4 * η ^ 2) * z ^ 2
  have hJ : Continuous J := by unfold J; fun_prop
  have hF : ContinuousOn F (Icc (0 : ℝ) 1) := by
    exact hJ.continuousOn.mul (hJ.continuousOn.log fun z hz => (bonusTransform_deriv_pos hη₀ hη₁ hz).ne')
  have hG : Continuous G := by unfold G; fun_prop
  have hle (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) : F z ≤ G z := by
    have hpos : 0 < J z := bonusTransform_deriv_pos hη₀ hη₁ hz
    have hl := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hpos) hpos.le
    calc
      F z ≤ J z * (J z - 1) := hl
      _ = G z := by unfold J G; ring
  have hbound : (∫ z in (0 : ℝ)..1, F z) ≤ ∫ z in (0 : ℝ)..1, G z := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · apply ContinuousOn.intervalIntegrable
      simpa [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hF
    · exact hG.intervalIntegrable _ _
    · exact hle
  have hg : (∫ z in (0 : ℝ)..1, G z) = η ^ 2 / 3 := by
    have ha : IntervalIntegrable (fun _ : ℝ => η + η ^ 2) volume 0 1 := by
      exact continuous_const.intervalIntegrable _ _
    have hb : IntervalIntegrable (fun z : ℝ => (-(2 * η) - 4 * η ^ 2) * z) volume 0 1 := by
      exact (continuous_const.mul continuous_id).intervalIntegrable _ _
    have hc : IntervalIntegrable (fun z : ℝ => (4 * η ^ 2) * z ^ 2) volume 0 1 := by
      exact (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable _ _
    unfold G
    rw [intervalIntegral.integral_add (ha.add hb) hc, intervalIntegral.integral_add ha hb,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_id,
      integral_pow, intervalIntegral.integral_const]
    norm_num
    ring
  exact hbound.trans_eq hg

/-- Lemma 4.7. The uniform law on the unit interval has divergence at most
η²/3 relative to its pushforward under the bonus transform. -/
theorem lemma_4_7 {η : ℝ} (hη₀ : 0 ≤ η) (hη₁ : η < 1) :
    let Q := volume.restrict (Icc (0 : ℝ) 1)
    klDiv Q (Q.map (bonusTransform η)) ≤ ENNReal.ofReal (η ^ 2 / 3) := by
  intro Q
  let J (z : ℝ) := 1 + η * (1 - 2 * z)
  let g (z : ℝ) := ENNReal.ofReal (J z)
  let h := bonusTransform η
  let Q' := Q.withDensity g
  have hmJ : Continuous J := by unfold J; fun_prop
  have hmg : Measurable g := hmJ.measurable.ennreal_ofReal
  have hmh : Continuous h := by unfold h bonusTransform; fun_prop
  have hmono : StrictMonoOn h (Icc (0 : ℝ) 1) := bonusTransform_strictMonoOn hη₀ hη₁
  have hpos (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : 0 < J x :=
    bonusTransform_deriv_pos hη₀ hη₁ hx
  have himage : h '' Icc (0 : ℝ) 1 = Icc (0 : ℝ) 1 := by
    rw [hmh.continuousOn.image_Icc_of_monotoneOn (show (0 : ℝ) ≤ 1 by norm_num)
      (StrictMonoOn.monotoneOn hmono)]
    simp [h, bonusTransform]
  have hmap : Q'.map h = Q := by
    ext s hs
    rw [Measure.map_apply hmh.measurable hs, withDensity_apply _ (hmh.measurable hs)]
    have hchange := lintegral_image_eq_lintegral_abs_deriv_mul
      (f := h) (f' := J) measurableSet_Icc
      (fun x _ => (bonusTransform_deriv η x).hasDerivWithinAt) hmono.injOn
      (s.indicator fun _ => (1 : ℝ≥0∞))
    rw [himage, lintegral_indicator hs] at hchange
    simp only [lintegral_const, one_mul, Measure.restrict_apply_univ] at hchange
    change _ = (volume.restrict (Icc (0 : ℝ) 1)) s
    rw [hchange, ← lintegral_indicator (hmh.measurable hs)]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with x hx
    by_cases hx' : h x ∈ s <;>
      simp [g, hx', abs_of_pos (hpos x hx)]
  have hac : Q' ≪ Q := withDensity_absolutelyContinuous _ _
  have hll : llr Q' Q =ᵐ[Q] fun z => Real.log (J z) := by
    filter_upwards [Measure.rnDeriv_withDensity Q hmg,
      ae_restrict_mem (μ := volume) measurableSet_Icc] with z hz hmem
    change Real.log ((Q'.rnDeriv Q z).toReal) = Real.log (J z)
    change Q'.rnDeriv Q z = g z at hz
    rw [hz, ENNReal.toReal_ofReal (hpos z hmem).le]
  have hlog : ContinuousOn (fun z => Real.log (J z)) (Icc (0 : ℝ) 1) :=
    hmJ.continuousOn.log fun z hz => (hpos z hz).ne'
  have hprod : Integrable (fun z => (g z).toReal • Real.log (J z)) Q := by
    have hc := hmJ.continuousOn.mul hlog
    apply (hc.integrableOn_compact isCompact_Icc).congr
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with z hz
    simp [g, ENNReal.toReal_ofReal (hpos z hz).le, smul_eq_mul]
  have hgfinite : ∀ᵐ z ∂Q, g z < ⊤ := ae_of_all _ fun _ => ENNReal.ofReal_lt_top
  have hli' : Integrable (fun z => Real.log (J z)) Q' :=
    (integrable_withDensity_iff_integrable_smul' hmg hgfinite).mpr hprod
  have hll' : llr Q' Q =ᵐ[Q'] fun z => Real.log (J z) := hll.filter_mono hac.ae_le
  have hli : Integrable (llr Q' Q) Q' := hli'.congr hll'.symm
  have hmass : Q' univ = Q univ := by
    rw [← hmap, Measure.map_apply hmh.measurable MeasurableSet.univ, preimage_univ]
  let : IsFiniteMeasure Q' := ⟨hmass ▸ measure_lt_top Q univ⟩
  have hi : (∫ z, llr Q' Q z ∂Q') ≤ η ^ 2 / 3 := by
    rw [integral_congr_ae hll',
      integral_withDensity_eq_integral_toReal_smul hmg hgfinite]
    have he : (∫ z, (g z).toReal • Real.log (J z) ∂Q) =
        ∫ z in (0 : ℝ)..1, J z * Real.log (J z) := by
      rw [intervalIntegral.integral_of_le (by norm_num), restrict_Ioc_eq_restrict_Icc]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with z hz
      simp [g, ENNReal.toReal_ofReal (hpos z hz).le, smul_eq_mul]
    rw [he]
    exact bonus_log_jacobian_integral_le hη₀ hη₁
  calc
    klDiv Q (Q.map h) ≤ klDiv Q' Q := hmap ▸ klDiv_map_le Q' Q hmh.measurable
    _ ≤ _ := by
      rw [klDiv_of_ac_of_integrable hac hli, show Q.real univ = Q'.real univ by
        simp only [measureReal_def, hmass], add_sub_cancel_right]
      exact ENNReal.ofReal_le_ofReal hi

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open MeasureTheory InformationTheory ProbabilityTheory Set
open scoped ENNReal

/-- Binary relative entropy, written using the continuous extension of
`x log x` at zero. The second parameter is in the open unit interval. -/
noncomputable def binaryEntropy (p q : ℝ) : ℝ :=
  p * Real.log p + (1 - p) * Real.log (1 - p)
    - p * Real.log q - (1 - p) * Real.log (1 - q)

/-- The binary form of Pinsker's inequality, including endpoint values of p. -/
theorem binaryEntropy_ge {p q : ℝ} (hp : p ∈ Icc 0 1) (hq : q ∈ Ioo 0 1) :
    2 * (p - q) ^ 2 ≤ binaryEntropy p q := by
  let f (x : ℝ) := binaryEntropy x q - 2 * (x - q) ^ 2
  let f' (x : ℝ) := Real.log x - Real.log (1 - x) - Real.log q + Real.log (1 - q) - 4 * (x - q)
  let f'' (x : ℝ) := x⁻¹ + (1 - x)⁻¹ - 4
  have ha : Continuous (fun x : ℝ => 1 - x) := continuous_const.sub continuous_id
  have hf : Continuous f :=
    (((Real.continuous_mul_log.add (Real.continuous_mul_log.comp ha)).sub (continuous_id.mul_const _)).sub
      (ha.mul_const _)).sub (((continuous_id.sub continuous_const).pow 2).const_mul 2)
  have hd (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt f (f' x) x := by
    have h1 := Real.hasDerivAt_mul_log hx.1.ne'
    have h2 := (Real.hasDerivAt_mul_log (sub_pos.mpr hx.2).ne').comp x
      ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x))
    have h3 := (hasDerivAt_id x).mul_const (Real.log q)
    have h4 := ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).mul_const (Real.log (1 - q))
    have h5 := (((hasDerivAt_id x).sub_const q).pow 2).const_mul 2
    convert (((h1.add h2).sub h3).sub h4).sub h5 using 1 <;>
      first | rfl | (dsimp [f']; norm_num; ring)
  have hdd (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt f' (f'' x) x := by
    have h1 := Real.hasDerivAt_log hx.1.ne'
    have h2 := (Real.hasDerivAt_log (sub_pos.mpr hx.2).ne').comp x
      ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x))
    have h3 := ((hasDerivAt_id x).sub_const q).const_mul 4
    convert (((h1.sub h2).sub_const (Real.log q)).add_const (Real.log (1 - q))).sub h3 using 1 <;>
      first | rfl | (dsimp [f'']; norm_num)
  have hpos (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : 0 ≤ f'' x := by
    have h1 : 0 < x := hx.1
    have h2 : 0 < 1 - x := sub_pos.mpr hx.2
    dsimp [f'']
    apply (le_of_mul_le_mul_right _ (mul_pos h1 h2))
    field_simp [h1.ne', h2.ne']
    nlinarith [sq_nonneg (2 * x - 1)]
  have hc : ConvexOn ℝ (Icc 0 1) f := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (f' := f') (f'' := f'') (convex_Icc _ _) hf.continuousOn
    · rw [interior_Icc]
      exact fun x hx => (hd x hx).hasDerivWithinAt
    · rw [interior_Icc]
      exact fun x hx => (hdd x hx).hasDerivWithinAt
    · rw [interior_Icc]
      exact hpos
  have hq' : q ∈ Icc 0 1 := ⟨hq.1.le, hq.2.le⟩
  have hz : f q = 0 := by dsimp [f, binaryEntropy]; ring
  have hdq : HasDerivAt f 0 q := by
    convert hd q hq using 1
    dsimp [f']
    ring
  apply sub_nonneg.mp
  change 0 ≤ f p
  rcases lt_trichotomy p q with h | rfl | h
  · have hs := hc.slope_le_of_hasDerivAt hp hq' h hdq
    rw [slope_def_field, hz] at hs
    exact sub_nonneg.mp (by simpa using (div_le_iff₀ (sub_pos.mpr h)).mp hs)
  · exact hz.ge
  · have hs := hc.le_slope_of_hasDerivAt hq' hp h hdq
    rw [slope_def_field, hz, sub_zero] at hs
    exact by simpa using (le_div_iff₀ (sub_pos.mpr h)).mp hs

private theorem mul_log_div_eq (p : ℝ) {q : ℝ} (hq : 0 < q) :
    p * Real.log (p / q) = p * Real.log p - p * Real.log q := by
  by_cases h : p = 0
  · simp [h]
  · rw [Real.log_div h hq.ne', mul_sub]

private theorem toReal_klDiv_bool (μ ν : Measure Bool) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hac : μ ≪ ν) (hq : ν.real {true} ∈ Ioo 0 1) :
    (klDiv μ ν).toReal = binaryEntropy (μ.real {true}) (ν.real {true}) := by
  have hcomp : ({true} : Set Bool)ᶜ = {false} := by ext b; cases b <;> simp
  have hfalse (ρ : Measure Bool) [IsProbabilityMeasure ρ] :
      ρ.real {false} = 1 - ρ.real {true} := by
    rw [← hcomp, measureReal_compl (measurableSet_singleton true), probReal_univ]
  have hν (b : Bool) : 0 < ν.real {b} := by
    cases b
    · rw [hfalse]
      exact sub_pos.mpr hq.2
    · exact hq.1
  have hrn (b : Bool) : (μ.rnDeriv ν b).toReal = μ.real {b} / ν.real {b} := by
    have h := Measure.setIntegral_toReal_rnDeriv hac {b}
    rw [integral_singleton, smul_eq_mul] at h
    apply (eq_div_iff (hν b).ne').mpr
    simpa only [mul_comm] using h
  have hsets : ({true} : Set Bool) ∪ {false} = univ := by ext b; cases b <;> simp
  have hInt : Integrable (llr μ ν) μ := by
    rw [← integrableOn_univ, ← hsets, integrableOn_union]
    exact ⟨integrableOn_singleton, integrableOn_singleton⟩
  rw [toReal_klDiv_of_measure_eq hac ((measure_univ : μ univ = 1).trans (measure_univ : ν univ = 1).symm), integral_fintype hInt, Fintype.univ_bool]
  simp only [Finset.sum_insert, Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true,
    Finset.sum_singleton, smul_eq_mul, llr, hrn]
  rw [mul_log_div_eq _ (hν true), mul_log_div_eq _ (hν false), hfalse μ, hfalse ν]
  unfold binaryEntropy
  ring

/-- For any measurable event, twice the squared difference of its
probabilities is at most the relative entropy of the two laws. -/
theorem event_difference_sq_le_klDiv {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {s : Set Ω} (hs : MeasurableSet s) :
    ENNReal.ofReal (2 * (μ.real s - ν.real s) ^ 2) ≤ klDiv μ ν := by
  classical
  by_cases htop : klDiv μ ν = ⊤
  · simp [htop]
  have hac := (klDiv_ne_top_iff.mp htop).1
  let p := μ.real s
  let q := ν.real s
  have hp : p ∈ Icc 0 1 :=
    ⟨measureReal_nonneg, (measureReal_mono (subset_univ s)).trans_eq probReal_univ⟩
  have hq : q ∈ Icc 0 1 :=
    ⟨measureReal_nonneg, (measureReal_mono (subset_univ s)).trans_eq probReal_univ⟩
  have hzero (h : q = 0) : p = q := by
    rw [h]
    exact (measureReal_eq_zero_iff (measure_ne_top _ _)).mpr (hac ((measureReal_eq_zero_iff (measure_ne_top _ _)).mp h))
  have hone (h : q = 1) : p = q := by
    have hν : ν.real sᶜ = 0 := by rw [measureReal_compl hs, probReal_univ]; exact sub_eq_zero.mpr h.symm
    have hμ : μ.real sᶜ = 0 := (measureReal_eq_zero_iff (measure_ne_top _ _)).mpr (hac ((measureReal_eq_zero_iff (measure_ne_top _ _)).mp hν))
    rw [measureReal_compl hs, probReal_univ] at hμ
    exact (sub_eq_zero.mp hμ).symm.trans h.symm
  change ENNReal.ofReal (2 * (p - q) ^ 2) ≤ _
  by_cases hqi : q ∈ Ioo 0 1
  swap
  · have he : p = q := by
      rcases lt_or_eq_of_le hq.1 with h₀ | h₀
      · exact hone (le_antisymm hq.2 (le_of_not_gt (fun h => hqi ⟨h₀, h⟩)))
      · exact hzero h₀.symm
    simp [he]
  let b (x : Ω) := if x ∈ s then true else false
  have hbm : Measurable b := Measurable.ite hs measurable_const measurable_const
  have _ : IsProbabilityMeasure (μ.map b) := Measure.isProbabilityMeasure_map hbm.aemeasurable
  have _ : IsProbabilityMeasure (ν.map b) := Measure.isProbabilityMeasure_map hbm.aemeasurable
  have hb : b ⁻¹' ({true} : Set Bool) = s := by ext x; simp [b]
  have hmap (ρ : Measure Ω) : (ρ.map b).real {true} = ρ.real s := by
    rw [measureReal_def, Measure.map_apply hbm (measurableSet_singleton true), hb, measureReal_def]
  have hle := klDiv_map_le μ ν hbm
  have hfin : klDiv (μ.map b) (ν.map b) ≠ ⊤ := ne_of_lt (hle.trans_lt (lt_top_iff_ne_top.mpr htop))
  have hbin := toReal_klDiv_bool (μ.map b) (ν.map b) (hac.map hbm)
    (by rwa [hmap])
  rw [hmap, hmap] at hbin
  exact ((ENNReal.ofReal_le_ofReal (binaryEntropy_ge hp hqi)).trans_eq
    (by rw [← hbin, ENNReal.ofReal_toReal hfin])).trans hle

/-- Appending an observation adds relative entropy only on the histories
where the learner queries the auxiliary action whose response law changed. -/
theorem klDiv_compProd_changed_on {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {s : Set α} (hs : MeasurableSet s) [DecidablePred (· ∈ s)]
    (Q Q' : Measure β) [IsProbabilityMeasure Q] [IsProbabilityMeasure Q']
    (hac : Q ≪ Q') (other : Kernel α β) [IsMarkovKernel other] :
    klDiv (μ ⊗ₘ Kernel.piecewise hs (Kernel.const α Q) other)
        (ν ⊗ₘ Kernel.piecewise hs (Kernel.const α Q') other) =
      klDiv μ ν + klDiv Q Q' * μ s := by
  let κ := Kernel.piecewise hs (Kernel.const α Q) other
  let κ' := Kernel.piecewise hs (Kernel.const α Q') other
  let d (p : α × β) := if p.1 ∈ s then Q.rnDeriv Q' p.2 else 1
  have hm : Measurable d := Measurable.ite (measurable_fst hs)
    ((Measure.measurable_rnDeriv Q Q').comp measurable_snd) measurable_const
  have hDensity : (μ ⊗ₘ κ').withDensity d = μ ⊗ₘ κ := by
    ext z hz
    rw [withDensity_apply _ hz, ← lintegral_indicator hz, Measure.lintegral_compProd (hm.indicator hz),
      Measure.compProd_apply hz]
    apply lintegral_congr
    intro a
    have hz' : MeasurableSet (Prod.mk a ⁻¹' z) := measurable_prodMk_left hz
    have he : (fun b => z.indicator d (a, b)) =
        (Prod.mk a ⁻¹' z).indicator (fun b => d (a, b)) := rfl
    rw [he, lintegral_indicator hz']
    by_cases ha : a ∈ s
    · simpa [d, κ, κ', Kernel.piecewise_apply, ha] using
        Measure.setLIntegral_rnDeriv hac (Prod.mk a ⁻¹' z)
    · simp [d, κ, κ', Kernel.piecewise_apply, ha]
  have hJoint : μ ⊗ₘ κ ≪ μ ⊗ₘ κ' := by
    rw [← hDensity]
    exact withDensity_absolutelyContinuous _ _
  have hrn : (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ κ') =ᵐ[μ ⊗ₘ κ'] d := by
    rw [← hDensity]
    exact Measure.rnDeriv_withDensity _ hm
  have hKL : klDiv (μ ⊗ₘ κ) (μ ⊗ₘ κ') = klDiv Q Q' * μ s := by
    rw [klDiv_eq_lintegral_klFun_of_ac hJoint]
    have he : (∫⁻ x, ENNReal.ofReal (klFun ((μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ κ') x).toReal) ∂(μ ⊗ₘ κ')) =
        ∫⁻ x, ENNReal.ofReal (klFun (d x).toReal) ∂(μ ⊗ₘ κ') := by
      apply lintegral_congr_ae
      filter_upwards [hrn] with x hx
      rw [hx]
    rw [he, Measure.lintegral_compProd (by fun_prop : Measurable (fun x => ENNReal.ofReal (klFun (d x).toReal)))]
    rw [← lintegral_indicator_const hs, klDiv_eq_lintegral_klFun_of_ac hac]
    apply lintegral_congr
    intro a
    by_cases ha : a ∈ s
    · simp [d, κ', Kernel.piecewise_apply, ha]
    · simp [d, κ', Kernel.piecewise_apply, ha, klFun]
  rw [show klDiv (μ ⊗ₘ κ) (ν ⊗ₘ κ') =
    klDiv μ ν + klDiv (μ ⊗ₘ κ) (μ ⊗ₘ κ') from klDiv_compProd_eq_add μ ν κ κ', hKL]

/-- Compare the expected numbers of plays of one action in two worlds.
Each event records whether the learner played that action in one round. -/
theorem expected_hits_le_of_klDiv {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (s : ι → Set Ω) (hs : ∀ i, MeasurableSet (s i))
    {D : ℝ} (hD : 0 ≤ D) (hkl : klDiv μ ν ≤ ENNReal.ofReal D) :
    (∑ i, ν.real (s i)) ≤ (∑ i, μ.real (s i)) + Fintype.card ι * Real.sqrt (D / 2) := by
  have hstep (i : ι) : ν.real (s i) ≤ μ.real (s i) + Real.sqrt (D / 2) := by
    have h := (event_difference_sq_le_klDiv μ ν (hs i)).trans hkl
    have hsq := (ENNReal.ofReal_le_ofReal_iff hD).mp h
    have hsqrt : ν.real (s i) - μ.real (s i) ≤ Real.sqrt (D / 2) :=
      Real.le_sqrt_of_sq_le (by nlinarith only [hsq])
    linarith only [hsqrt]
  simpa [Finset.sum_add_distrib] using Finset.sum_le_sum (s := (Finset.univ : Finset ι))
    (fun i _ => hstep i)

/-- The one-period count transfer in Lemma 4.8. Once the history divergence has
been bounded by the baseline count, this is the required comparison of play counts. -/
theorem expected_auxiliary_hits_le {Ω : Type*} [MeasurableSpace Ω] {R : ℕ}
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (s : Fin R → Set Ω) (hs : ∀ i, MeasurableSet (s i))
    {η : ℝ} (hη : 0 ≤ η)
    (hkl : klDiv μ ν ≤ ENNReal.ofReal (η ^ 2 / 3 * ∑ i, μ.real (s i))) :
    let baseline := ∑ i, μ.real (s i)
    (∑ i, ν.real (s i)) ≤ baseline + η * R * Real.sqrt (baseline / 6) := by
  intro baseline
  have hbase : 0 ≤ baseline := Finset.sum_nonneg fun _ _ => measureReal_nonneg
  have hD : 0 ≤ η ^ 2 / 3 * baseline := by positivity
  have h := expected_hits_le_of_klDiv μ ν s hs hD hkl
  rw [show η ^ 2 / 3 * baseline / 2 = η ^ 2 * (baseline / 6) by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hη, Fintype.card_fin] at h
  linarith only [h, show (R : ℝ) * (η * Real.sqrt (baseline / 6)) =
    η * R * Real.sqrt (baseline / 6) by ring]

end CalibeatBandit

end

section

set_option autoImplicit false
set_option maxHeartbeats 150000

open Matrix MeasureTheory
open scoped BigOperators

namespace CalibeatBandit

section Measurability

variable {Ω : Type*} [MeasurableSpace Ω] {K : ℕ}

theorem measurable_select {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] {a : Ω → α} (ha : Measurable a)
    {f : α → Ω → ℝ} (hf : ∀ i, Measurable (f i)) :
    Measurable (fun ω => f (a ω) ω) := by
  classical
  have heq : (fun ω => f (a ω) ω) =
      fun ω => ∑ i, if a ω = i then f i ω else 0 := by
    funext ω
    simp
  rw [heq]
  exact Finset.measurable_sum _ fun i _ => Measurable.ite (ha (measurableSet_singleton i)) (hf i) measurable_const

end Measurability

end CalibeatBandit

end

section

set_option autoImplicit false

open Filter MeasureTheory
open scoped BigOperators

namespace CalibeatBandit

theorem integrable_of_abs_bound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {f : Ω → ℝ} (hm : Measurable f) {B : ℝ}
    (hb : ∀ ω, |f ω| ≤ B) : Integrable f P :=
  (integrable_const B).mono' hm.aestronglyMeasurable
    (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hb ω)

theorem integral_exp_sum_le_one {T : ℕ} {Ω : Type*}
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (info preDraw : ℕ → MeasurableSpace Ω)
    (hinfo : ∀ a b, a ≤ b → b ≤ T → info a ≤ info b)
    (hinfo_le : ∀ n ≤ T, info n ≤ mΩ)
    (hpre : ∀ n < T, preDraw n ≤ mΩ)
    (hprev : ∀ n < T, info n ≤ preDraw n)
    (d : ℕ → Ω → ℝ) {B : ℝ}
    (hm : ∀ t < T, Measurable[info (t + 1)] (d t))
    (hb : ∀ t < T, ∀ ω, |d t ω| ≤ B)
    (hc : ∀ t < T, condExp (preDraw t) P (fun ω => Real.exp (d t ω)) ≤ᵐ[P] fun _ => 1) :
    ∫ ω, Real.exp (∑ t ∈ Finset.range T, d t ω) ∂P ≤ 1 := by
  let F (n : ℕ) (ω : Ω) := Real.exp (∑ t ∈ Finset.range n, d t ω)
  have hF (n : ℕ) (hn : n ≤ T) : Measurable[info n] (F n) := by
    refine Real.continuous_exp.measurable.comp (Finset.measurable_sum _ fun t ht => ?_)
    have hs := Nat.succ_le_of_lt (Finset.mem_range.mp ht)
    exact (hm t (lt_of_lt_of_le (Finset.mem_range.mp ht) hn)).mono
      (hinfo _ _ hs hn) le_rfl
  have hi (n : ℕ) (hn : n ≤ T) : Integrable (F n) P := by
    apply integrable_of_abs_bound ((hF n hn).mono (hinfo_le n hn) le_rfl)
    intro ω
    rw [show F n ω = Real.exp (∑ t ∈ Finset.range n, d t ω) from rfl,
      abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ ∑ _ ∈ Finset.range n, B := Finset.sum_le_sum fun t ht =>
        (le_abs_self _).trans (hb t ((Finset.mem_range.mp ht).trans_le hn) ω)
      _ = (n : ℝ) * B := by simp
  have step (n : ℕ) (hn : n < T) : (∫ ω, F (n + 1) ω ∂P) ≤ ∫ ω, F n ω ∂P := by
    let G : Ω → ℝ := fun ω => Real.exp (d n ω)
    have hG : Integrable G P := by
      refine integrable_of_abs_bound (B := Real.exp B) (Real.continuous_exp.measurable.comp
        ((hm n hn).mono (hinfo_le _ (Nat.succ_le_of_lt hn)) le_rfl)) ?_
      intro ω
      change |Real.exp (d n ω)| ≤ Real.exp B
      rw [abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hb n hn ω))
    have heq : F (n + 1) = F n * G := by
      funext ω
      simp [F, G, Finset.sum_range_succ, Real.exp_add]
    have hprod : Integrable (F n * G) P := heq ▸ hi (n + 1) (Nat.succ_le_of_lt hn)
    have hpull := condExp_mul_of_stronglyMeasurable_left
      ((hF n hn.le).mono (hprev n hn) le_rfl).stronglyMeasurable
      hprod hG
    rw [heq, ← integral_condExp (m := preDraw n) (hpre n hn)]
    apply integral_mono_ae integrable_condExp (hi n hn.le)
    filter_upwards [hpull, hc n hn] with ω hw hcω
    rw [hw]
    exact mul_le_of_le_one_right (Real.exp_nonneg _) hcω
  have hbound (n : ℕ) (hn : n ≤ T) : (∫ ω, F n ω ∂P) ≤ 1 := by
    induction n with
    | zero => simp [F]
    | succ n ih =>
      have hh : n < T := Nat.lt_of_succ_le hn
      exact (step n hh).trans (ih hh.le)
  exact hbound T le_rfl

theorem integrable_finset_max {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} [IsFiniteMeasure P] (hne : (Finset.univ : Finset ι).Nonempty)
    (F : ι → Ω → ℝ) {B : ℝ} (hm : ∀ i, Measurable (F i)) (hb : ∀ i ω, |F i ω| ≤ B) :
    Integrable (fun ω => Finset.univ.sup' hne (fun i => F i ω)) P := by
  let _ : Nonempty ι := hne.to_subtype.map Subtype.val
  apply integrable_of_abs_bound
  · simp_rw [Finset.sup'_univ_eq_ciSup]
    exact Measurable.iSup hm
  · intro ω
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' hne (fun i => F i ω)
    exact hi.symm ▸ hb i ω

/-- A finite maximum is bounded in expectation by the logarithm of the number
of competitors whenever each competitor has an exponential moment at most one. -/
theorem integral_max_le_log_card {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (hne : (Finset.univ : Finset ι).Nonempty)
    (F : ι → Ω → ℝ) {η B : ℝ} (hη : 0 < η)
    (hm : ∀ i, Measurable (F i)) (hb : ∀ i ω, |F i ω| ≤ B)
    (he : ∀ i, ∫ ω, Real.exp (η * F i ω) ∂P ≤ 1) :
    ∫ ω, Finset.univ.sup' hne (fun i => F i ω) ∂P ≤ Real.log (Fintype.card ι) / η := by
  classical
  let M (ω : Ω) := Finset.univ.sup' hne (fun i => F i ω)
  let Z (ω : Ω) := ∑ i, Real.exp (η * F i ω)
  let N : ℝ := Fintype.card ι
  let H (ω : Ω) := Real.log N + (Z ω / N - 1)
  let _ : Nonempty ι := hne.to_subtype.map Subtype.val
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast Fintype.card_pos (α := ι)
  have hM : Integrable M P := integrable_finset_max hne F hm hb
  have hei (i : ι) : Integrable (fun ω => Real.exp (η * F i ω)) P := by
    refine integrable_of_abs_bound (B := Real.exp (η * B))
      (Real.continuous_exp.measurable.comp ((hm i).const_mul η)) ?_
    intro ω
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hb i ω)) hη.le)
  have hZ : Integrable Z P := integrable_finsetSum _ fun i _ => hei i
  have hZi : (∫ ω, Z ω ∂P) ≤ N := by
    rw [show (∫ ω, Z ω ∂P) = ∑ i, ∫ ω, Real.exp (η * F i ω) ∂P from
      integral_finsetSum _ (fun i _ => hei i)]
    calc
      _ ≤ ∑ _ : ι, (1 : ℝ) := Finset.sum_le_sum fun i _ => he i
      _ = N := by simp [N]
  have hH : Integrable H P := (integrable_const _).add ((hZ.div_const N).sub (integrable_const _))
  have hpoint (ω : Ω) : η * M ω ≤ H ω := by
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' hne (fun i => F i ω)
    have hle : Real.exp (η * M ω) ≤ Z ω := by
      change Real.exp (η * Finset.univ.sup' hne (fun i => F i ω)) ≤ Z ω
      rw [hi]
      exact Finset.single_le_sum (fun j _ => Real.exp_nonneg (η * F j ω)) (Finset.mem_univ i)
    have hz : 0 < Z ω := (Real.exp_pos _).trans_le hle
    have hl := Real.log_le_log (Real.exp_pos _) hle
    rw [Real.log_exp] at hl
    have hh := Real.log_le_sub_one_of_pos (div_pos hz hN)
    rw [Real.log_div hz.ne' hN.ne'] at hh
    dsimp [H]
    linarith only [hl, hh]
  have hHi : (∫ ω, H ω ∂P) ≤ Real.log N := by
    let W : Ω → ℝ := fun ω => Z ω / N
    change (∫ ω, Real.log N + (W ω - 1) ∂P) ≤ _
    have hW : Integrable W P := hZ.div_const N
    have hdiff : Integrable (fun ω => W ω - 1) P := hW.sub (integrable_const _)
    rw [integral_add (integrable_const _) hdiff, integral_sub hW (integrable_const _)]
    dsimp only [W]
    rw [integral_div]
    simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
    linarith only [(div_le_one hN).mpr hZi]
  have hi := (integral_mono (hM.const_mul η) hH hpoint).trans hHi
  have heq : (∫ ω, η * M ω ∂P) = η * ∫ ω, M ω ∂P := integral_const_mul η M
  rw [heq] at hi
  exact (le_div_iff₀ hη).mpr (by simpa only [mul_comm] using hi)

end CalibeatBandit

end

section

set_option autoImplicit false

open Filter MeasureTheory
open scoped BigOperators

namespace CalibeatBandit

private theorem condExp_exp_centered_le_one {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {X : Ω → ℝ} (hX : Measurable[mΩ] X) (hb : ∀ ω, |X ω| ≤ 1)
    (hc : condExp m P X =ᵐ[P] 0) (s : ℝ) :
    condExp m P (fun ω => Real.exp (s * X ω - s ^ 2 / 2)) ≤ᵐ[P] fun _ => 1 := by
  let k := Real.exp (-(s ^ 2 / 2))
  let A := k * Real.cosh s
  let B := k * Real.sinh s
  have hi : Integrable X P := @integrable_of_abs_bound Ω mΩ P _ X hX 1 hb
  have he : Integrable (fun ω => Real.exp (s * X ω - s ^ 2 / 2)) P := by
    refine @integrable_of_abs_bound Ω mΩ P _ _ (Real.continuous_exp.measurable.comp
      ((hX.const_mul s).sub measurable_const)) (Real.exp |s|) fun ω => ?_
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ s * X ω := sub_le_self _ (by positivity)
      _ ≤ |s * X ω| := le_abs_self _
      _ ≤ |s| := by rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (hb ω)
  have heq (ω : Ω) : Real.exp (s * X ω - s ^ 2 / 2) ≤ A + B * X ω := by
    rw [sub_eq_add_neg, Real.exp_add, mul_comm (Real.exp _)]
    have h := mul_le_mul_of_nonneg_left (Real.exp_mul_le_cosh_add_mul_sinh (hb ω) s)
      (Real.exp_nonneg (-(s ^ 2 / 2)))
    have hleft : Real.exp (-(s ^ 2 / 2)) * Real.exp (s * X ω) =
        Real.exp (-(s ^ 2 / 2)) * Real.exp (X ω * s) := by rw [mul_comm s]
    rw [hleft]
    exact h.trans_eq (by unfold A B k; ring)
  have hA : Integrable (fun _ : Ω => A) P := integrable_const _
  have hB : Integrable (fun ω => B * X ω) P := hi.const_mul B
  have hcond := condExp_mono (m := m) he (hA.add hB) (ae_of_all _ heq)
  have hbPull : condExp m P (fun ω => B * X ω) =ᵐ[P] fun ω => B * condExp m P X ω :=
    condExp_mul_of_stronglyMeasurable_left stronglyMeasurable_const hB hi
  have hconst : A ≤ 1 := by
    calc
      A ≤ k * Real.exp (s ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left (Real.cosh_le_exp_half_sq s) (Real.exp_nonneg _)
      _ = 1 := by unfold k; rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  filter_upwards [hcond, condExp_add hA hB m, hbPull, hc] with ω h₁ h₂ h₃ h₄
  apply h₁.trans
  rw [h₂]
  change condExp m P (fun _ : Ω => A) ω + condExp m P (fun ω => B * X ω) ω ≤ 1
  simpa only [condExp_const hm, h₃, h₄, Pi.zero_apply, mul_zero, add_zero] using hconst

/-- Lemma 4.10 for increments bounded by one. The two signs of each
martingale index the competitors in the exponential maximum. -/
theorem martingale_max_abs_le {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
    [Fintype ι] [Nonempty ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (info : Filtration ℕ mΩ) {T : ℕ} (hT : 0 < T) (d : ℕ → ι → Ω → ℝ)
    (hm : ∀ t < T, ∀ j, Measurable[info (t + 1)] (d t j))
    (hb : ∀ t < T, ∀ j ω, |d t j ω| ≤ 1)
    (hc : ∀ t < T, ∀ j, condExp (info t) P (d t j) =ᵐ[P] 0) :
    (∫ ω, Finset.univ.sup' Finset.univ_nonempty
      (fun j => |∑ t ∈ Finset.range T, d t j ω|) ∂P) ≤
      Real.sqrt (2 * T * Real.log (2 * Fintype.card ι)) := by
  classical
  let L := Real.log (2 * Fintype.card ι)
  have hL : 0 < L := by
    apply Real.log_pos
    have h : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos (α := ι)
    linarith
  have ht : 0 < (T : ℝ) := by exact_mod_cast hT
  let R := Real.sqrt (2 * T * L)
  have hrad : 0 < 2 * T * L := by positivity
  have hR : 0 < R := Real.sqrt_pos.mpr hrad
  let s := R / T
  have hs : 0 < s := div_pos hR ht
  let X (t : ℕ) (j : ι × Bool) : Ω → ℝ := if j.2 then d t j.1 else -d t j.1
  have hXm (t : ℕ) (ht : t < T) (j : ι × Bool) : Measurable[info (t + 1)] (X t j) := by
    unfold X
    split
    · exact hm t ht j.1
    · exact (hm t ht j.1).neg
  have hXb (t : ℕ) (ht : t < T) (j : ι × Bool) (ω : Ω) : |X t j ω| ≤ 1 := by
    unfold X
    split <;> simpa using hb t ht j.1 ω
  have hXc (t : ℕ) (ht : t < T) (j : ι × Bool) : condExp (info t) P (X t j) =ᵐ[P] 0 := by
    unfold X
    split
    · exact hc t ht j.1
    · filter_upwards [condExp_neg (μ := P) (m := info t) (f := d t j.1), hc t ht j.1] with ω h he
      simp [h, he]
  let F (j : ι × Bool) (ω : Ω) := ∑ t ∈ Finset.range T, (X t j ω - s / 2)
  have hfm (j : ι × Bool) : Measurable (F j) :=
    Finset.measurable_sum _ fun t ht =>
      ((hXm t (Finset.mem_range.mp ht) j).mono (info.le _) le_rfl).sub measurable_const
  have hfb (j : ι × Bool) (ω : Ω) : |F j ω| ≤ T * (1 + |s / 2|) := by
    calc
      _ ≤ ∑ t ∈ Finset.range T, |X t j ω - s / 2| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ ∈ Finset.range T, (1 + |s / 2|) := Finset.sum_le_sum fun t ht =>
        (abs_sub _ _).trans (add_le_add_left (hXb t (Finset.mem_range.mp ht) j ω) _)
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hExp (j : ι × Bool) : (∫ ω, Real.exp (s * F j ω) ∂P) ≤ 1 := by
    have h := integral_exp_sum_le_one P info info
      (fun _ _ h _ => info.mono h) (fun n _ => info.le n) (fun n _ => info.le n) (fun _ _ => le_rfl)
      (fun t ω => s * X t j ω - s ^ 2 / 2)
      (B := |s| + |s ^ 2 / 2|)
      (fun t ht => ((hXm t ht j).const_mul s).sub measurable_const)
      (fun t ht ω => (abs_sub _ _).trans (by
        rw [abs_mul]
        exact add_le_add_left (mul_le_of_le_one_right (abs_nonneg _) (hXb t ht j ω)) _))
      (fun t ht => condExp_exp_centered_le_one (info.le t)
        ((hXm t ht j).mono (info.le _) le_rfl) (hXb t ht j) (hXc t ht j) s)
    have heq (ω : Ω) : s * F j ω =
        ∑ t ∈ Finset.range T, (s * X t j ω - s ^ 2 / 2) := by
      simp only [F, Finset.mul_sum]
      exact Finset.sum_congr rfl fun t _ => by ring
    simpa only [heq] using h
  have hF := integral_max_le_log_card P Finset.univ_nonempty F hs hfm hfb hExp
  let M (ω : Ω) := Finset.univ.sup' Finset.univ_nonempty
      (fun j : ι => |∑ t ∈ Finset.range T, d t j ω|)
  have hiM : Integrable M P := by
    apply integrable_finset_max Finset.univ_nonempty (B := T)
    · intro j
      have hmeas : Measurable (fun ω => ∑ t ∈ Finset.range T, d t j ω) :=
        Finset.measurable_sum _ fun t ht => (hm t (Finset.mem_range.mp ht) j).mono (info.le _) le_rfl
      exact continuous_abs.measurable.comp hmeas
    · intro j ω
      rw [abs_abs]
      calc
        _ ≤ ∑ t ∈ Finset.range T, |d t j ω| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _ ∈ Finset.range T, (1 : ℝ) :=
          Finset.sum_le_sum fun t ht => hb t (Finset.mem_range.mp ht) j ω
        _ = _ := by simp
  have hf (ω : Ω) (j : ι) (b : Bool) :
      F (j, b) ω = (if b then ∑ t ∈ Finset.range T, d t j ω
      else -(∑ t ∈ Finset.range T, d t j ω)) - T * (s / 2) := by
    cases b <;> simp [F, X, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  have hM (ω : Ω) : Finset.univ.sup' Finset.univ_nonempty (fun j => F j ω) = M ω - T * (s / 2) := by
    apply le_antisymm
    · refine Finset.sup'_le _ _ fun ⟨j, b⟩ _ => ?_
      rw [hf]
      apply sub_le_sub_right
      refine le_trans ?_ (Finset.le_sup' (fun j => |∑ t ∈ Finset.range T, d t j ω|) (Finset.mem_univ j))
      cases b <;> simp [le_abs_self, neg_le_abs]
    · obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
        (fun j : ι => |∑ t ∈ Finset.range T, d t j ω|)
      change M ω = _ at hj
      rw [hj]
      let z := ∑ t ∈ Finset.range T, d t j ω
      change |z| - _ ≤ _
      by_cases hz : 0 ≤ z
      · rw [abs_of_nonneg hz, ← show F (j, true) ω = z - T * (s / 2) by simpa only [if_true] using hf ω j true]
        exact Finset.le_sup' (fun j => F j ω) (Finset.mem_univ (j, true))
      · rw [abs_of_neg (lt_of_not_ge hz), ← show F (j, false) ω = -z - T * (s / 2) by
            simpa only [Bool.false_eq_true, if_false] using hf ω j false]
        exact Finset.le_sup' (fun j => F j ω) (Finset.mem_univ (j, false))
  simp_rw [hM, Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat, mul_comm _ (2 : ℝ)] at hF
  rw [integral_sub hiM (integrable_const (T * (s / 2)))] at hF
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul] at hF
  change (∫ ω, M ω ∂P) - T * (s / 2) ≤ L / s at hF
  have hRsq : R ^ 2 = 2 * T * L := Real.sq_sqrt hrad.le
  have hhalf : L / s = R / 2 := by
    apply (div_eq_iff hs.ne').mpr
    dsimp [s]
    field_simp [ht.ne']
    nlinarith only [hRsq]
  have hother : (T : ℝ) * (s / 2) = R / 2 := by
    dsimp [s]
    field_simp [ht.ne']
  rw [hhalf, hother] at hF
  change (∫ ω, M ω ∂P) ≤ R
  linarith only [hF]

/-- Lemma 4.10 with an arbitrary positive bound on the increments. -/
theorem lemma_4_10 {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
    [Fintype ι] [Nonempty ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (info : Filtration ℕ mΩ) {T : ℕ} {c : ℝ} (hc : 0 < c)
    (d : ℕ → ι → Ω → ℝ)
    (hm : ∀ t < T, ∀ j, Measurable[info (t + 1)] (d t j))
    (hb : ∀ t < T, ∀ j ω, |d t j ω| ≤ c)
    (hcenter : ∀ t < T, ∀ j, condExp (info t) P (d t j) =ᵐ[P] 0) :
    (∫ ω, Finset.univ.sup' Finset.univ_nonempty
      (fun j => |∑ t ∈ Finset.range T, d t j ω|) ∂P) ≤
      c * Real.sqrt (2 * T * Real.log (2 * Fintype.card ι)) := by
  by_cases hT : T = 0
  · subst T
    simp
  let X (t : ℕ) (j : ι) (ω : Ω) := d t j ω / c
  have hXm (t : ℕ) (ht : t < T) (j : ι) : Measurable[info (t + 1)] (X t j) :=
    (hm t ht j).div_const c
  have hXb (t : ℕ) (ht : t < T) (j : ι) (ω : Ω) : |X t j ω| ≤ 1 := by
    change |d t j ω / c| ≤ 1
    rw [abs_div, abs_of_pos hc]
    exact (div_le_one hc).mpr (hb t ht j ω)
  have hXc (t : ℕ) (ht : t < T) (j : ι) : condExp (info t) P (X t j) =ᵐ[P] 0 := by
    have hi : Integrable (d t j) P :=
      integrable_of_abs_bound ((hm t ht j).mono (info.le _) le_rfl) (hb t ht j)
    have hprod : Integrable ((fun _ : Ω => c⁻¹) * d t j) P := hi.const_mul _
    have heq : X t j = (fun _ : Ω => c⁻¹) * d t j := by
      funext ω
      simp only [X, Pi.mul_apply, div_eq_inv_mul]
    rw [heq]
    have hmconst : StronglyMeasurable[info t] (fun _ : Ω => c⁻¹) := stronglyMeasurable_const
    filter_upwards [condExp_mul_of_stronglyMeasurable_left hmconst hprod hi,
      hcenter t ht j] with ω h₁ h₂
    simp [h₁, h₂]
  have h := martingale_max_abs_le P info (Nat.pos_of_ne_zero hT) X hXm hXb hXc
  have hscale (ω : Ω) :
      Finset.univ.sup' Finset.univ_nonempty (fun j => |∑ t ∈ Finset.range T, d t j ω|) =
        c * Finset.univ.sup' Finset.univ_nonempty (fun j => |∑ t ∈ Finset.range T, X t j ω|) := by
    let F (j : ι) := |∑ t ∈ Finset.range T, X t j ω|
    have hj (j : ι) : |∑ t ∈ Finset.range T, d t j ω| = c * F j := by
      unfold F X
      rw [← Finset.sum_div, abs_div, abs_of_pos hc]
      field_simp
    simp_rw [hj]
    apply le_antisymm
    · refine Finset.sup'_le _ _ fun j hj => ?_
      exact mul_le_mul_of_nonneg_left (Finset.le_sup' F hj) hc.le
    · obtain ⟨j, hj, heq⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty F
      rw [heq]
      exact Finset.le_sup' (fun j => c * F j) hj
  simp_rw [hscale]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left h hc.le

end CalibeatBandit

end

section

set_option autoImplicit false

open Filter MeasureTheory Matrix
open scoped BigOperators

namespace CalibeatBandit

def swapGain {K : ℕ} (T : ℕ) (q u : ℕ → Fin K → ℝ) (i j : Fin K) : ℝ :=
  ∑ t ∈ Finset.range T, q t i * (u t j - u t i)

def bestSwapGain {K : ℕ} (T : ℕ) (q u : ℕ → Fin K → ℝ) (i : Fin K) : ℝ :=
  Finset.univ.sup' ⟨i, Finset.mem_univ i⟩ (swapGain T q u i)

theorem swapGain_le_best {K T : ℕ} (q u : ℕ → Fin K → ℝ) (i j : Fin K) :
    swapGain T q u i j ≤ bestSwapGain T q u i :=
  Finset.le_sup' (swapGain T q u i) (Finset.mem_univ j)

theorem bestSwapGain_nonneg {K T : ℕ} (q u : ℕ → Fin K → ℝ) (i : Fin K) :
    0 ≤ bestSwapGain T q u i := by
  simpa [swapGain] using swapGain_le_best (T := T) q u i i

/-- The swap map can maximize every row independently. -/
theorem pseudoSwapRegret_eq_sum_bestSwapGain {K : ℕ} (T : ℕ) (q u : ℕ → Fin K → ℝ) :
    pseudoSwapRegret T q u = ∑ i, bestSwapGain T q u i := by
  classical
  have score (f : Fin K → Fin K) :
      (∑ t ∈ Finset.range T, ((∑ i, q t i * u t (f i)) - q t ⬝ᵥ u t)) =
        ∑ i, swapGain T q u i (f i) := by
    unfold swapGain dotProduct
    have h (t : ℕ) : (∑ i, q t i * u t (f i)) - ∑ i, q t i * u t i =
        ∑ i, q t i * (u t (f i) - u t i) := by
      simp only [mul_sub, Finset.sum_sub_distrib]
    simp_rw [h]
    exact Finset.sum_comm
  unfold pseudoSwapRegret
  simp_rw [score]
  apply le_antisymm
  · exact Finset.sup'_le _ _ fun f _ => Finset.sum_le_sum fun i _ => swapGain_le_best q u i (f i)
  · have exists_best (i : Fin K) : ∃ j, bestSwapGain T q u i = swapGain T q u i j := by
      obtain ⟨j, _, h⟩ := Finset.exists_mem_eq_sup' ⟨i, Finset.mem_univ i⟩ (swapGain T q u i)
      exact ⟨j, h⟩
    choose f hf using exists_best
    calc
      _ = ∑ i, swapGain T q u i (f i) := Finset.sum_congr rfl fun i _ => hf i
      _ ≤ _ := Finset.le_sup' (fun f : Fin K → Fin K => ∑ i, swapGain T q u i (f i))
        (Finset.mem_univ f)

/-- The deterministic root comparison used in Lemma 4.4. -/
theorem root_bestSwapGain {K T : ℕ} (q u : ℕ → Fin K → ℝ)
    (i rootA rootB : Fin K) (H : ℝ)
    (hroot : ∀ t < T, u t rootA + u t rootB = 1 / (2 * H)) :
    (∑ t ∈ Finset.range T, q t i) / (4 * H) -
      (∑ t ∈ Finset.range T, q t i * u t i) ≤ bestSwapGain T q u i := by
  have hsum : swapGain T q u i rootA + swapGain T q u i rootB =
      (∑ t ∈ Finset.range T, q t i) * (1 / (2 * H)) -
        2 * (∑ t ∈ Finset.range T, q t i * u t i) := by
    simp only [swapGain, ← Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun t ht => by
      rw [← hroot t (Finset.mem_range.mp ht)]
      ring
  have half : (∑ t ∈ Finset.range T, q t i) / (4 * H) =
      ((∑ t ∈ Finset.range T, q t i) * (1 / (2 * H))) / 2 := by
    by_cases h : H = 0
    · simp [h]
    · field_simp
      ring
  linarith only [half, hsum, swapGain_le_best (T := T) q u i rootA,
    swapGain_le_best (T := T) q u i rootB]

theorem unnamed_bestSwapGain {K T : ℕ} (q u : ℕ → Fin K → ℝ)
    (i rootA rootB : Fin K) (H : ℝ)
    (hi : ∀ t < T, u t i = 0)
    (hroot : ∀ t < T, u t rootA + u t rootB = 1 / (2 * H)) :
    (∑ t ∈ Finset.range T, q t i) / (4 * H) ≤ bestSwapGain T q u i := by
  have hzero : (∑ t ∈ Finset.range T, q t i * u t i) = 0 :=
    Finset.sum_eq_zero fun t ht => by rw [hi t (Finset.mem_range.mp ht), mul_zero]
  simpa only [hzero, sub_zero] using root_bestSwapGain q u i rootA rootB H hroot

/-- The two deterministic comparisons used for a leaf action in Lemma 4.5.
The selected auxiliary action has bonus probability one in the leaf's period. -/
theorem leaf_bestSwapGain {K T : ℕ} (q u : ℕ → Fin K → ℝ)
    (period : Finset ℕ) (hperiod : period ⊆ Finset.range T)
    (i auxiliary rootA rootB : Fin K) (H : ℝ)
    (hq : ∀ t < T, 0 ≤ q t i) (hu : ∀ t < T, 0 ≤ u t auxiliary)
    (hoff : ∀ t < T, t ∉ period → u t i = 0)
    (hon : ∀ t ∈ period, u t auxiliary = 1)
    (hroot : ∀ t < T, u t rootA + u t rootB = 1 / (2 * H)) :
    (∑ t ∈ period, q t i * (1 - u t i)) ≤ bestSwapGain T q u i ∧
      (∑ t ∈ Finset.range T, q t i) / (4 * H) -
        (∑ t ∈ period, q t i * u t i) ≤ bestSwapGain T q u i := by
  classical
  constructor
  · apply le_trans _ (swapGain_le_best (T := T) q u i auxiliary)
    unfold swapGain
    have h := Finset.sum_le_sum_of_subset_of_nonneg hperiod
      (f := fun t => q t i * (u t auxiliary - u t i))
      (fun t ht hout => by
        rw [hoff t (Finset.mem_range.mp ht) hout, sub_zero]
        exact mul_nonneg (hq t (Finset.mem_range.mp ht)) (hu t (Finset.mem_range.mp ht)))
    have he : (∑ t ∈ period, q t i * (1 - u t i)) =
        ∑ t ∈ period, q t i * (u t auxiliary - u t i) :=
      Finset.sum_congr rfl fun t ht => by rw [hon t ht]
    exact he.le.trans h
  · have he : (∑ t ∈ period, q t i * u t i) = ∑ t ∈ Finset.range T, q t i * u t i := by
      apply Finset.sum_subset hperiod
      intro t ht hout
      rw [hoff t (Finset.mem_range.mp ht) hout, mul_zero]
    rw [he]
    exact root_bestSwapGain q u i rootA rootB H hroot

/-- After averaging over the fresh leaf coin, the two leaf comparisons give
the factor 1/(8H) in Lemma 4.5. -/
theorem leaf_expected_gain {H total inside gain : ℝ} (h₁ : inside / 2 ≤ gain)
    (h₂ : total / (4 * H) - inside / 2 ≤ gain) :
    total / (8 * H) ≤ gain := by
  have he : total / (4 * H) = 2 * (total / (8 * H)) := by ring
  linarith only [h₁, h₂, he]

/-- The case split of Lemma 4.9 after taking expectations. The two groups
partition the learner's play mass, and their swap gains are nonnegative. -/
theorem aggregate_swap_gain {T auxMass auxGain otherGain H : ℝ}
    (hT : 0 ≤ T) (hH : 1 ≤ H)
    (haux₀ : 0 ≤ auxGain) (hother₀ : 0 ≤ otherGain)
    (haux : auxMass / (4 * H) - T / (64 * H) ≤ auxGain)
    (hother : (T - auxMass) / (184 * H ^ 5) ≤ otherGain) :
    T / (368 * H ^ 5) ≤ auxGain + otherGain := by
  have hH₀ : 0 < H := by linarith
  have hpos : 0 < 184 * H ^ 5 := by positivity
  by_cases h : auxMass ≤ T / 2
  · calc
      _ = (T / 2) / (184 * H ^ 5) := by ring
      _ ≤ (T - auxMass) / (184 * H ^ 5) :=
        div_le_div_of_nonneg_right (by linarith) hpos.le
      _ ≤ otherGain := hother
      _ ≤ _ := le_add_of_nonneg_left haux₀
  · have hh : H ≤ H ^ 5 := by
      calc
        H = H * 1 := (mul_one _).symm
        _ ≤ H * H ^ 4 := mul_le_mul_of_nonneg_left (one_le_pow₀ hH) hH₀.le
        _ = _ := by ring
    have hbig : 64 * H ≤ 368 * H ^ 5 := by linarith
    have hm : T / (368 * H ^ 5) ≤ T / (64 * H) :=
      div_le_div_of_nonneg_left hT (by positivity) hbig
    have haux' : T / (8 * H) ≤ auxMass / (4 * H) := by
      rw [show T / (8 * H) = (T / 2) / (4 * H) by ring]
      exact div_le_div_of_nonneg_right (le_of_not_ge h) (by positivity)
    have heq : T / (8 * H) = 8 * (T / (64 * H)) := by ring
    have hn : 0 ≤ T / (64 * H) := by positivity
    linarith only [hm, haux', heq, hn, haux, hother₀]

/-- Averaging the one-period comparison between the baseline world and the
worlds with a selected auxiliary action. Here `baseline j` is the expected
number of plays of action j under the baseline law. -/
theorem auxiliary_average_le {M : ℕ} (hM : 0 < M) {period η : ℝ}
    (hperiod : 0 ≤ period) (hη : 0 ≤ η)
    (baseline selected : Fin M → ℝ) (hbase : ∀ j, 0 ≤ baseline j)
    (hcounts : (∑ j, baseline j) ≤ period)
    (hcompare : ∀ j, selected j ≤ baseline j + η * period * Real.sqrt (baseline j / 6)) :
    (∑ j, selected j) / M ≤ period / M + η * period * Real.sqrt (period / (6 * M)) := by
  have hM' : 0 < (M : ℝ) := by exact_mod_cast hM
  have hs : (∑ j, Real.sqrt (baseline j)) ≤ Real.sqrt (M * period) := by
    have h := Real.sum_sqrt_mul_sqrt_le (s := (Finset.univ : Finset (Fin M)))
      (f := baseline) (g := fun _ => 1) hbase (fun _ => zero_le_one)
    simp only [Real.sqrt_one, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at h
    calc
      _ ≤ Real.sqrt (∑ j, baseline j) * Real.sqrt M := by simpa only [mul_one] using h
      _ ≤ Real.sqrt period * Real.sqrt M :=
        mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hcounts) (Real.sqrt_nonneg _)
      _ = _ := by rw [mul_comm, ← Real.sqrt_mul hM'.le]
  have hall := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin M))) fun j _ => hcompare j
  simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum, Real.sqrt_div (hbase _),
    ← Finset.sum_div] at hall
  calc
    _ ≤ (period + η * period * (Real.sqrt (M * period) / Real.sqrt 6)) / M := by
      apply div_le_div_of_nonneg_right _ hM'.le
      exact hall.trans (add_le_add hcounts (mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hs (Real.sqrt_nonneg _)) (mul_nonneg hη hperiod)))
    _ = _ := by
      rw [add_div, mul_div_assoc, div_div, Real.sqrt_mul hM'.le,
        Real.sqrt_div hperiod, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 6)]
      have hsM : (Real.sqrt M) ^ 2 = M := Real.sq_sqrt hM'.le
      have hpM : 0 < Real.sqrt M := Real.sqrt_pos.mpr hM'
      have hp6 : 0 < Real.sqrt (6 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
      rw [← hsM]
      rw [Real.sqrt_sq hpM.le]
      field_simp

/-- The conversion from the proxy swap gain to realized swap regret.
The error for each action is bounded by its largest row deviation. -/
theorem swapRegret_ge_proxy {K T : ℕ} (a : ℝ)
    (q u y : ℕ → Fin K → ℝ) (I : ℕ → Fin K) :
    a * pseudoSwapRegret T q u -
      (∑ i : Fin K, Finset.univ.sup' ⟨i, Finset.mem_univ i⟩ (fun j =>
        |swapGain T (fun t => Pi.single (I t) 1) y i j - a * swapGain T q u i j|)) ≤
      swapRegret T y I := by
  classical
  let played (t : ℕ) : Fin K → ℝ := Pi.single (I t) 1
  have hplayed : swapRegret T y I = pseudoSwapRegret T played y := by
    unfold swapRegret pseudoSwapRegret
    simp [played, dotProduct, Pi.single_apply, Finset.sum_ite_eq']
  rw [hplayed, pseudoSwapRegret_eq_sum_bestSwapGain, pseudoSwapRegret_eq_sum_bestSwapGain,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i _
  obtain ⟨j, hj, heq⟩ := Finset.exists_mem_eq_sup' ⟨i, Finset.mem_univ i⟩ (swapGain T q u i)
  change bestSwapGain T q u i = swapGain T q u i j at heq
  have herr := Finset.le_sup' (fun j => |swapGain T played y i j - a * swapGain T q u i j|) hj
  change a * bestSwapGain T q u i -
      Finset.univ.sup' ⟨i, Finset.mem_univ i⟩ (fun j =>
        |swapGain T played y i j - a * swapGain T q u i j|) ≤ bestSwapGain T played y i
  rw [heq]
  have h₁ := neg_le_abs (swapGain T played y i j - a * swapGain T q u i j)
  have h₂ := swapGain_le_best (T := T) played y i j
  linarith only [herr, h₁, h₂]

set_option maxHeartbeats 450000 in
/-- The final martingale comparison for the discrete lower bound. Each
increment is the observed swap gain minus its conditional prediction. -/
theorem expected_swapRegret_ge_proxy {K T : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (info : Filtration ℕ mΩ)
    (anchor : Fin K) (a c : ℝ) (hc : 0 < c)
    (q u y : Ω → ℕ → Fin K → ℝ) (I : Ω → ℕ → Fin K)
    (hy : ∀ t < T, ∀ ω j, y ω t j ∈ Set.Icc (0 : ℝ) 1)
    (hym : ∀ t < T, ∀ j, Measurable (fun ω => y ω t j))
    (hI : ∀ t < T, Measurable (fun ω => I ω t))
    (hq : ∀ t < T, ∀ ω, IsProbVec (q ω t))
    (hu : ∀ t < T, ∀ ω j, u ω t j ∈ Set.Icc (0 : ℝ) 1)
    (hqm : ∀ t < T, ∀ j, Measurable (fun ω => q ω t j))
    (hum : ∀ t < T, ∀ j, Measurable (fun ω => u ω t j)) :
    let d (i : Fin K) (t : ℕ) (j : Fin K) (ω : Ω) :=
      (Pi.single (I ω t) (1 : ℝ) : Fin K → ℝ) i * (y ω t j - y ω t i) -
        a * (q ω t i * (u ω t j - u ω t i))
    (∀ t < T, ∀ i j, Measurable[info (t + 1)] (d i t j)) →
    (∀ t < T, ∀ i j ω, |d i t j ω| ≤ c) →
    (∀ t < T, ∀ i j, condExp (info t) P (d i t j) =ᵐ[P] 0) →
    a * (∫ ω, pseudoSwapRegret T (q ω) (u ω) ∂P) -
      K * (c * Real.sqrt (2 * T * Real.log (2 * K))) ≤
      ∫ ω, swapRegret T (y ω) (I ω) ∂P := by
  classical
  intro d hdm hdb hdc
  let _ : Nonempty (Fin K) := ⟨anchor⟩
  let D (i : Fin K) (ω : Ω) :=
    Finset.univ.sup' Finset.univ_nonempty (fun j => |∑ t ∈ Finset.range T, d i t j ω|)
  have hD (i : Fin K) : Integrable (D i) P := by
    apply integrable_finset_max Finset.univ_nonempty _ (B := (T : ℝ) * c)
    · intro j
      have h : Measurable (fun ω => ∑ t ∈ Finset.range T, d i t j ω) :=
        Finset.measurable_sum _ fun t ht =>
          (hdm t (Finset.mem_range.mp ht) i j).mono (info.le _) le_rfl
      exact continuous_abs.measurable.comp h
    · intro j ω
      rw [abs_abs]
      calc
        _ ≤ ∑ t ∈ Finset.range T, |d i t j ω| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _ ∈ Finset.range T, c := Finset.sum_le_sum fun t ht =>
          hdb t (Finset.mem_range.mp ht) i j ω
        _ = _ := by simp
  have d_bound (i : Fin K) : ∫ ω, D i ω ∂P ≤ c * Real.sqrt (2 * T * Real.log (2 * K)) := by
    simpa only [Fintype.card_fin] using lemma_4_10 P info hc (d i)
      (fun t ht j => hdm t ht i j) (fun t ht j => hdb t ht i j) (fun t ht j => hdc t ht i j)
  have sum_bound (F : ℕ → Ω → ℝ) (hF : ∀ t < T, ∀ ω, |F t ω| ≤ 1) (ω : Ω) :
      |∑ t ∈ Finset.range T, F t ω| ≤ (T : ℝ) := by
    calc
      _ ≤ ∑ t ∈ Finset.range T, |F t ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ ∈ Finset.range T, (1 : ℝ) := Finset.sum_le_sum fun t ht =>
        hF t (Finset.mem_range.mp ht) ω
      _ = _ := by simp
  have diff_bound {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
      |x - y| ≤ 1 := abs_le.mpr ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩
  have hreal : Integrable (fun ω => swapRegret T (y ω) (I ω)) P := by
    unfold swapRegret
    apply integrable_finset_max ⟨id, Finset.mem_univ _⟩ _ (B := T)
    · intro f
      exact Finset.measurable_sum _ fun t ht =>
        (measurable_select (hI t (Finset.mem_range.mp ht)) (fun j => hym t (Finset.mem_range.mp ht) (f j))).sub
          (measurable_select (hI t (Finset.mem_range.mp ht)) (hym t (Finset.mem_range.mp ht)))
    · intro f ω
      exact sum_bound (fun t ω => y ω t (f (I ω t)) - y ω t (I ω t))
        (fun t ht ω => diff_bound (hy t ht ω _) (hy t ht ω _)) ω
  have hproxy : Integrable (fun ω => pseudoSwapRegret T (q ω) (u ω)) P := by
    unfold pseudoSwapRegret
    apply integrable_finset_max ⟨id, Finset.mem_univ _⟩ _ (B := T)
    · intro f
      exact Finset.measurable_sum _ fun t ht =>
        (Finset.measurable_sum _ fun i _ => (hqm t (Finset.mem_range.mp ht) i).mul
          (hum t (Finset.mem_range.mp ht) (f i))).sub (Finset.measurable_sum _ fun i _ =>
          (hqm t (Finset.mem_range.mp ht) i).mul (hum t (Finset.mem_range.mp ht) i))
    · intro f ω
      apply sum_bound (fun t ω => (∑ i, q ω t i * u ω t (f i)) - q ω t ⬝ᵥ u ω t) _ ω
      intro t ht ω
      have he : (∑ i, q ω t i * u ω t (f i)) - q ω t ⬝ᵥ u ω t =
          ∑ i, q ω t i * (u ω t (f i) - u ω t i) := by
        simp only [dotProduct, mul_sub, Finset.sum_sub_distrib]
      rw [he]
      calc
        _ ≤ ∑ i, |q ω t i * (u ω t (f i) - u ω t i)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, q ω t i := Finset.sum_le_sum fun i _ => by
          rw [abs_mul, abs_of_nonneg ((hq t ht ω).1 i)]
          exact mul_le_of_le_one_right ((hq t ht ω).1 i) (diff_bound (hu t ht ω _) (hu t ht ω _))
        _ = 1 := (hq t ht ω).2
  have heq (ω : Ω) (i : Fin K) :
      Finset.univ.sup' ⟨i, Finset.mem_univ i⟩ (fun j =>
        |swapGain T (fun t => Pi.single (I ω t) 1) (y ω) i j -
          a * swapGain T (q ω) (u ω) i j|) = D i ω := by
    unfold D
    congr 1
    funext j
    congr 1
    simp only [d, swapGain, Finset.mul_sum, Finset.sum_sub_distrib]
  have hp (ω : Ω) := swapRegret_ge_proxy (T := T) a (q ω) (u ω) (y ω) (I ω)
  simp_rw [heq] at hp
  have hi : Integrable (fun ω => ∑ i, D i ω) P := integrable_finsetSum _ fun i _ => hD i
  have hi' : Integrable (fun ω => a * pseudoSwapRegret T (q ω) (u ω) - ∑ i, D i ω) P :=
    (hproxy.const_mul a).sub hi
  have hle := integral_mono hi' hreal hp
  have h' : (∫ ω, a * pseudoSwapRegret T (q ω) (u ω) - ∑ i, D i ω ∂P) =
      a * (∫ ω, pseudoSwapRegret T (q ω) (u ω) ∂P) - ∑ i, ∫ ω, D i ω ∂P := by
    rw [integral_sub (hproxy.const_mul a) hi, integral_const_mul, integral_finsetSum _ (fun i _ => hD i)]
  rw [h'] at hle
  have hs : (∑ i, ∫ ω, D i ω ∂P) ≤ K * (c * Real.sqrt (2 * T * Real.log (2 * K))) := by
    calc
      _ ≤ ∑ _ : Fin K, c * Real.sqrt (2 * T * Real.log (2 * K)) :=
        Finset.sum_le_sum fun i _ => d_bound i
      _ = _ := by simp
  linarith only [hs, hle]

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal Function

/-- A one-period experiment for a designated auxiliary action. The query
event is determined by the transcript, and the two worlds use the same
observation kernel whenever this action is not queried. -/
structure AuxiliaryExperiment where
  query : (t : ℕ) → Set (FeedbackHistory t)
  measurable_query : ∀ t, MeasurableSet (query t)
  other : (t : ℕ) → Kernel (FeedbackHistory t) ℝ
  markov_other : ∀ t, IsMarkovKernel (other t)

namespace AuxiliaryExperiment

noncomputable def step (X : AuxiliaryExperiment) (Q : Measure ℝ) (t : ℕ) :
    Kernel (FeedbackHistory t) ℝ := by
  classical
  exact Kernel.piecewise (X.measurable_query t) (Kernel.const _ Q) (X.other t)

instance markov_step (X : AuxiliaryExperiment) (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (t : ℕ) : IsMarkovKernel (X.step Q t) := by
  classical
  let _ : IsMarkovKernel (X.other t) := X.markov_other t
  unfold step
  infer_instance

noncomputable def law (X : AuxiliaryExperiment) (Q : Measure ℝ) :
    (t : ℕ) → Measure (FeedbackHistory t)
  | 0 => Measure.dirac ()
  | t + 1 => X.law Q t ⊗ₘ X.step Q t

instance probability_law (X : AuxiliaryExperiment) (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (t : ℕ) : IsProbabilityMeasure (X.law Q t) := by
  induction t with
  | zero => change IsProbabilityMeasure (Measure.dirac ()); infer_instance
  | succ t ih =>
    let _ := ih
    change IsProbabilityMeasure (X.law Q t ⊗ₘ X.step Q t)
    infer_instance

/-- In a transcript of length r, this event records the learner's action
in round i, which depends only on the observations before round i. -/
def hit (X : AuxiliaryExperiment) : (r : ℕ) → Fin r → Set (FeedbackHistory r)
  | 0, i => Fin.elim0 i
  | r + 1, i => Fin.lastCases (Prod.fst ⁻¹' X.query r) (fun j => Prod.fst ⁻¹' X.hit r j) i

theorem measurable_hit (X : AuxiliaryExperiment) (r : ℕ) (i : Fin r) :
    MeasurableSet (X.hit r i) := by
  induction r with
  | zero => exact Fin.elim0 i
  | succ r ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [hit, Fin.lastCases_last]
      exact measurable_fst (X.measurable_query r)
    · rw [hit, Fin.lastCases_castSucc]
      exact measurable_fst (ih j)

private theorem measure_of_preimage_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsFiniteMeasure μ] (κ : Kernel α β) [IsMarkovKernel κ]
    (s : Set α) (hs : MeasurableSet s) :
    (μ ⊗ₘ κ) (Prod.fst ⁻¹' s) = μ s := by
  rw [← Measure.map_apply measurable_fst hs, ← Measure.fst, Measure.fst_compProd]

theorem law_hit (X : AuxiliaryExperiment) (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (r : ℕ) (i : Fin r) :
    X.law Q r (X.hit r i) = X.law Q i (X.query i) := by
  induction r with
  | zero => exact Fin.elim0 i
  | succ r ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [hit, Fin.lastCases_last, Fin.val_last]
      exact measure_of_preimage_fst (X.law Q r) (X.step Q r)
        (X.query r) (X.measurable_query r)
    · rw [hit, Fin.lastCases_castSucc, Fin.val_castSucc]
      exact (measure_of_preimage_fst (X.law Q r) (X.step Q r) (X.hit r j)
        (X.measurable_hit r j)).trans (ih j)

/-- The transcript divergence is the one-observation divergence times the
expected number of times the changed action is queried in the baseline world. -/
theorem klDiv_law (X : AuxiliaryExperiment) (Q Q' : Measure ℝ)
    [IsProbabilityMeasure Q] [IsProbabilityMeasure Q'] (hac : Q ≪ Q') (r : ℕ) :
    klDiv (X.law Q r) (X.law Q' r) =
      klDiv Q Q' * ∑ i : Fin r, X.law Q r (X.hit r i) := by
  induction r with
  | zero =>
    rw [Fin.sum_univ_zero, mul_zero]
    exact klDiv_self (X.law Q 0)
  | succ r ih =>
    classical
    let _ : IsMarkovKernel (X.other r) := X.markov_other r
    have h := klDiv_compProd_changed_on (X.law Q r) (X.law Q' r)
      (X.measurable_query r) Q Q' hac (X.other r)
    calc
      _ = klDiv (X.law Q r) (X.law Q' r) + klDiv Q Q' * X.law Q r (X.query r) := h
      _ = _ := by
        rw [ih, ← mul_add]
        congr 1
        simp only [law_hit]
        rw [Fin.sum_univ_castSucc]
        simp

/-- Lemma 4.8's one-period comparison for a single auxiliary action. -/
theorem bonus_hit_bound (X : AuxiliaryExperiment) {η : ℝ} (hη : 0 ≤ η) (hη₁ : η < 1)
    (r : ℕ) :
    let Q : Measure ℝ := volume.restrict (Icc 0 1)
    let Q' := Q.map (bonusTransform η)
    let baseline := ∑ i : Fin r, (X.law Q r).real (X.hit r i)
    (∑ i : Fin r, (X.law Q' r).real (X.hit r i)) ≤
      baseline + η * r * Real.sqrt (baseline / 6) := by
  intro Q Q' baseline
  have _ : IsProbabilityMeasure Q := ⟨by simp [Q, Real.volume_Icc]⟩
  have hm : Measurable (bonusTransform η) := by unfold bonusTransform; fun_prop
  have _ : IsProbabilityMeasure Q' := Measure.isProbabilityMeasure_map hm.aemeasurable
  have hbonus : klDiv Q Q' ≤ ENNReal.ofReal (η ^ 2 / 3) := lemma_4_7 hη hη₁
  have hfin : klDiv Q Q' ≠ ⊤ := ne_of_lt (hbonus.trans_lt ENNReal.ofReal_lt_top)
  have hac := (klDiv_ne_top_iff.mp hfin).1
  apply expected_auxiliary_hits_le (X.law Q r) (X.law Q' r) (X.hit r) (X.measurable_hit r) hη
  rw [X.klDiv_law Q Q' hac, ENNReal.ofReal_mul (by positivity : 0 ≤ η ^ 2 / 3),
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => measureReal_nonneg)]
  simp_rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  gcongr

/-- Two experiments with the same observation kernels have the same law. -/
theorem law_eq_of_step_eq (X Y : AuxiliaryExperiment) (Q : Measure ℝ)
    (h : ∀ t, X.step Q t = Y.step Q t) (r : ℕ) : X.law Q r = Y.law Q r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change X.law Q r ⊗ₘ X.step Q r = Y.law Q r ⊗ₘ Y.step Q r
    rw [ih, h]

end AuxiliaryExperiment

/-- A period with a fixed private seed. The learner's action is a
measurable function of the reward transcript in that period. -/
structure AuxiliaryPeriod (K M : ℕ) where
  pick : (t : ℕ) → FeedbackHistory t → Fin K
  measurable_pick : ∀ t, Measurable (pick t)
  aux : Fin M ↪ Fin K
  base : (t : ℕ) → Kernel (FeedbackHistory t) ℝ
  markov_base : ∀ t, IsMarkovKernel (base t)

namespace AuxiliaryPeriod

def experiment {K M : ℕ} (A : AuxiliaryPeriod K M) (j : Fin M) : AuxiliaryExperiment where
  query := fun t => A.pick t ⁻¹' {A.aux j}
  measurable_query := fun t => A.measurable_pick t (measurableSet_singleton _)
  other := A.base
  markov_other := A.markov_base

theorem step_base {K M : ℕ} (A : AuxiliaryPeriod K M) (Q : Measure ℝ)
    (hbase : ∀ t h j, A.pick t h = A.aux j → A.base t h = Q) (j : Fin M) (t : ℕ) :
    (A.experiment j).step Q t = A.base t := by
  classical
  ext h s hs
  rw [AuxiliaryExperiment.step, Kernel.piecewise_apply']
  by_cases he : A.pick t h = A.aux j
  · simp [experiment, he, hbase t h j he]
  · simp [experiment, he]

/-- If each auxiliary action gives a base-law observation in the baseline
world, a uniform choice of the bonus action yields the one-period bound
from Lemma 4.8. -/
theorem average_bonus_hits_le {K M : ℕ} (A : AuxiliaryPeriod K M) (hM : 0 < M)
    (r : ℕ) {η : ℝ} (hη : 0 ≤ η) (hη₁ : η < 1) :
    let Q : Measure ℝ := volume.restrict (Icc 0 1)
    let Q' := Q.map (bonusTransform η)
    (∀ t h j, A.pick t h = A.aux j → A.base t h = Q) →
    (∑ j : Fin M, ∑ i : Fin r, ((A.experiment j).law Q' r).real ((A.experiment j).hit r i)) / M
      ≤ (r : ℝ) / M + η * r * Real.sqrt ((r : ℝ) / (6 * M)) := by
  intro Q Q' hbase
  let j₀ : Fin M := ⟨0, hM⟩
  let baseline (j : Fin M) := ∑ i : Fin r, ((A.experiment j).law Q r).real ((A.experiment j).hit r i)
  let selected (j : Fin M) := ∑ i : Fin r, ((A.experiment j).law Q' r).real ((A.experiment j).hit r i)
  have _ : IsProbabilityMeasure Q := ⟨by simp [Q, Real.volume_Icc]⟩
  have hnonneg (j : Fin M) : 0 ≤ baseline j := Finset.sum_nonneg fun _ _ => measureReal_nonneg
  have hbaseline (j : Fin M) (t : ℕ) : (A.experiment j).law Q t = (A.experiment j₀).law Q t :=
    AuxiliaryExperiment.law_eq_of_step_eq _ _ Q
      (fun u => (A.step_base Q hbase j u).trans (A.step_base Q hbase j₀ u).symm) t
  have hmass (i : Fin r) :
      (∑ j : Fin M, ((A.experiment j₀).law Q i).real ((A.experiment j).query i)) ≤ 1 := by
    let μ := (A.experiment j₀).law Q i
    let s := fun j => (A.experiment j).query i
    have hd : Pairwise (Disjoint on s) := by
      intro j k hjk
      refine Set.disjoint_left.mpr fun h hj hk => hjk ?_
      apply A.aux.injective
      exact ((Set.mem_singleton_iff.mp hj).symm.trans (Set.mem_singleton_iff.mp hk))
    rw [← measureReal_iUnion_fintype (μ := μ) hd (fun j => (A.experiment j).measurable_query i)]
    exact (measureReal_mono (subset_univ _)).trans_eq probReal_univ
  have hcounts : (∑ j, baseline j) ≤ (r : ℝ) := by
    have he (j : Fin M) (i : Fin r) :
        ((A.experiment j).law Q r).real ((A.experiment j).hit r i) =
        ((A.experiment j₀).law Q i).real ((A.experiment j).query i) := by
      rw [measureReal_def, (A.experiment j).law_hit Q r i, hbaseline, measureReal_def]
    simp only [baseline, he]
    rw [Finset.sum_comm]
    simpa using Finset.sum_le_sum (s := (Finset.univ : Finset (Fin r))) (fun i _ => hmass i)
  exact auxiliary_average_le hM (Nat.cast_nonneg r) hη baseline selected hnonneg hcounts
    (fun j => (A.experiment j).bonus_hit_bound hη hη₁ r)

end AuxiliaryPeriod

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open Set MeasureTheory

namespace TreeNode

def root (h : ℕ) : TreeNode h := ⟨0, 0⟩

theorem root_active {h : ℕ} (l : Fin (2 ^ h)) : (root h).active l := by
  exact ⟨by simp [first, root], by simp [last, root]⟩

theorem active_leaf_iff {h : ℕ} (v : TreeNode h) (hd : (v.1 : ℕ) = h) (l : Fin (2 ^ h)) :
    v.active l ↔ (l : ℕ) = (v.2 : ℕ) := by
  simp [active, first, last, hd]
  omega

/-- Children are numbered consecutively within the next level. -/
def child {h : ℕ} (v : TreeNode h) (hd : (v.1 : ℕ) < h) (right : Bool) : TreeNode h :=
  ⟨⟨(v.1 : ℕ) + 1, by omega⟩, ⟨2 * (v.2 : ℕ) + if right then 1 else 0, by
    have hv := v.2.isLt
    change _ < 2 ^ ((v.1 : ℕ) + 1)
    rw [pow_succ]
    cases right <;> simp <;> omega⟩⟩

theorem child_edges {h : ℕ} (v : TreeNode h) (hd : (v.1 : ℕ) < h) :
    (v.child hd false).first = v.first ∧ (v.child hd false).last = v.mid ∧
      (v.child hd true).first = v.mid ∧ (v.child hd true).last = v.last := by
  have hsub : h - (v.1 : ℕ) = (h - ((v.1 : ℕ) + 1)) + 1 := by omega
  simp only [child, first, last, mid, Bool.false_eq_true, ↓reduceIte, add_zero]
  rw [hsub, pow_succ]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

theorem child_active_iff {h : ℕ} (v : TreeNode h) (hd : (v.1 : ℕ) < h)
    (leaf : Fin (2 ^ h)) :
    ((v.child hd false).active leaf ↔ v.active leaf ∧ (leaf : ℕ) < v.mid) ∧
      ((v.child hd true).active leaf ↔ v.active leaf ∧ v.mid ≤ (leaf : ℕ)) := by
  obtain ⟨hfl, hll, hfr, hlr⟩ := v.child_edges hd
  have hle : v.first ≤ v.mid := Nat.le_add_right _ _
  have hmid : v.mid ≤ v.last := by
    rw [← hfr, ← hlr]
    exact Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  simp only [active, hfl, hll, hfr, hlr]
  omega

end TreeNode

theorem treeBonusProb_mem {h M U : ℕ} (leaf : Fin (2 ^ h))
    (coin : TreeNode h → Bool) (leafCoin : Bool) (selected : Fin M) (a : TreeAction h M U) :
    treeBonusProb leaf coin leafCoin selected a ∈ Icc (0 : ℝ) 1 := by
  have hz : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have h₁ : (1 : ℝ) ∈ Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  rcases a with ⟨v, side⟩ | (j | j)
  · have hdepth : (v.1 : ℕ) ≤ h := Nat.le_of_lt_succ v.1.isLt
    have hd : ((v.1 : ℕ) : ℝ) ≤ h := by exact_mod_cast hdepth
    have hh : 0 < treeHeight h := by unfold treeHeight; positivity
    have hfrac : (((v.1 : ℕ) + 1 : ℝ) / (2 * treeHeight h)) ∈ Icc 0 1 := by
      refine ⟨by positivity, (div_le_one (by positivity)).mpr ?_⟩
      unfold treeHeight
      linarith
    simp only [treeBonusProb]
    split_ifs <;> assumption
  · simp only [treeBonusProb]
    split <;> assumption
  · exact hz

theorem treeBonusProb_root_pair {h M U : ℕ} (hh : 0 < h) (leaf : Fin (2 ^ h))
    (coin : TreeNode h → Bool) (leafCoin : Bool) (selected : Fin M) :
    treeBonusProb (U := U) leaf coin leafCoin selected (.inl (TreeNode.root h, false)) +
      treeBonusProb (U := U) leaf coin leafCoin selected (.inl (TreeNode.root h, true)) =
      1 / (2 * treeHeight h) := by
  have hd : ((TreeNode.root h).1 : ℕ) ≠ h := by simpa [TreeNode.root] using hh.ne
  let b := if (leaf : ℕ) < (TreeNode.root h).mid then false else coin (TreeNode.root h)
  change (if (TreeNode.root h).active leaf then
      if ((TreeNode.root h).1 : ℕ) = h then (if false = leafCoin then 1 else 0)
      else if false = b then _ else 0 else 0) + _ = _
  simp only [treeBonusProb, TreeNode.root_active, if_true, hd, if_false]
  change (if false = b then _ else 0) + (if true = b then _ else 0) = _
  cases b <;> simp [TreeNode.root]

theorem treeBonusProb_leaf_pair {h M U : ℕ} (leaf : Fin (2 ^ h))
    (v : TreeNode h) (hd : (v.1 : ℕ) = h) (ha : v.active leaf)
    (coin : TreeNode h → Bool) (leafCoin : Bool) (selected : Fin M) :
    treeBonusProb (U := U) leaf coin leafCoin selected (.inl (v, false)) +
      treeBonusProb (U := U) leaf coin leafCoin selected (.inl (v, true)) = 1 := by
  cases leafCoin <;> simp [treeBonusProb, ha, hd]

/-- A change of one fixed node coin has no effect before the first leaf
in that node's right subtree. -/
theorem treeBonusProb_update_before_right {h M U : ℕ} (leaf : Fin (2 ^ h))
    (v : TreeNode h) (hleaf : (leaf : ℕ) < v.mid)
    (coin : TreeNode h → Bool) (b leafCoin : Bool) (selected : Fin M) (a : TreeAction h M U) :
    treeBonusProb leaf (Function.update coin v b) leafCoin selected a =
      treeBonusProb leaf coin leafCoin selected a := by
  rcases a with ⟨w, side⟩ | a
  · by_cases hw : w = v
    · subst w
      simp [treeBonusProb, hleaf]
    · simp [treeBonusProb, Function.update_of_ne hw]
  · cases a <;> rfl

theorem feedbackHistory_eq_of_prior_rewards_eq {A : Type*}
    (pick : (t : ℕ) → FeedbackHistory t → A) (y y' : ℕ → A → ℝ) (t : ℕ)
    (h : ∀ s < t, ∀ a, y s a = y' s a) :
    feedbackHistory pick y t = feedbackHistory pick y' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have he := ih (fun s hs => h s (Nat.lt_succ_of_lt hs))
    simp only [feedbackHistory, he, h t (Nat.lt_succ_self t)]
    rfl

/-- Changing a node's coin leaves the learner's action unchanged through
the first round that coin can affect. The leaves are visited in order. -/
theorem action_eq_of_update_before_right {h M U : ℕ}
    (pick : (t : ℕ) → FeedbackHistory t → TreeAction h M U)
    (active : ℕ → Fin (2 ^ h)) (v : TreeNode h) (b : Bool)
    (η : ℝ) (coin : TreeNode h → Bool) (leafCoin : ℕ → Bool)
    (selected : Fin (2 ^ h) → Fin M) (z : ℕ → Icc (0 : ℝ) 1)
    (draw : ℕ → TreeAction h M U → Ico (0 : ℝ) 1) (t : ℕ)
    (hprior : ∀ s < t, (active s : ℕ) < v.mid) :
    let y (c : TreeNode h → Bool) (s : ℕ) :=
      treeReward η (active s) c (leafCoin s) (selected (active s)) (z s) (draw s)
    pick t (feedbackHistory pick (y (Function.update coin v b)) t) =
      pick t (feedbackHistory pick (y coin) t) := by
  intro y
  congr 1
  apply feedbackHistory_eq_of_prior_rewards_eq
  intro s hs a
  dsimp [y, treeReward]
  rw [treeBonusProb_update_before_right (active s) v (hprior s hs)]

/-- A quantity that is invariant under changing one fair coin has half
its total mass in each value of that coin. -/
theorem sum_on_fair_coin {ι : Type*} [Fintype ι] [DecidableEq ι]
    (j : ι) (b : Bool) (g : (ι → Bool) → ℝ)
    (hg : ∀ c v, g (Function.update c j v) = g c) :
    (∑ c : ι → Bool, if c j = b then g c else 0) = (∑ c, g c) / 2 := by
  let flip (c : ι → Bool) := Function.update c j (! c j)
  have hflip : Function.Involutive flip := by
    intro c
    funext k
    by_cases hk : k = j
    · subst k
      simp [flip]
    · simp [flip, Function.update_of_ne hk]
  let e : (ι → Bool) ≃ (ι → Bool) := ⟨flip, flip, hflip, hflip⟩
  let f (c : ι → Bool) := if c j = b then g c else 0
  have he (c : ι → Bool) : f (e c) = if c j ≠ b then g c else 0 := by
    change (if flip c j = b then g (flip c) else 0) = _
    have hfg : g (flip c) = g c := hg c _
    have hfj : flip c j = ! c j := by simp [flip]
    rw [hfg, hfj]
    cases b <;> cases c j <;> simp
  have hs := e.sum_comp f
  simp_rw [he] at hs
  have hadd (c : ι → Bool) : g c =
      (if c j = b then g c else 0) + (if c j ≠ b then g c else 0) := by
    by_cases h : c j = b <;> simp [h]
  have htotal : (∑ c, g c) = (∑ c, f c) + (∑ c, if c j ≠ b then g c else 0) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => hadd c
  change (∑ c, f c) = _
  linarith only [htotal, hs]

/-- Extract a single oblivious environment from a randomized construction.
The two independent seeds describe the environment and the learner. -/
theorem exists_environment_of_seedwise_lower_bound {Ω S : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] (μ : Measure Ω) (ν : Measure S)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (regret : Ω × S → ℝ)
    (hi : Integrable regret (μ.prod ν)) {b : ℝ}
    (h : ∀ s, b ≤ ∫ ω, regret (ω, s) ∂μ) :
    ∃ ω, b ≤ ∫ s, regret (ω, s) ∂ν := by
  let g (ω : Ω) := ∫ s, regret (ω, s) ∂ν
  have hgi : Integrable g μ := hi.integral_prod_left
  have hmean : b ≤ ∫ ω, g ω ∂μ := by
    rw [← integral_prod regret hi, integral_prod_symm regret hi]
    simpa using integral_mono (integrable_const b) hi.swap.integral_prod_left h
  by_contra! hs
  have hp (ω : Ω) : 0 < b - g ω := sub_pos.mpr (hs ω)
  have hfull : Function.support (fun ω => b - g ω) = Set.univ := by
    ext ω
    simp [Function.mem_support, (hp ω).ne']
  have hpos := (integral_pos_iff_support_of_nonneg (fun ω => (hp ω).le)
    ((integrable_const b).sub hgi)).mpr (by rw [hfull, measure_univ]; exact (zero_lt_one : (0 : ENNReal) < 1))
  rw [integral_sub (integrable_const _) hgi] at hpos
  simp only [integral_const, probReal_univ, one_smul] at hpos
  linarith

/-- The child comparison for a right-action at a deepest internal node
(Case 4 in Appendix D.1). It holds for every realization of the coins. -/
theorem deepest_right_gain {h M U N T : ℕ} (e : Fin N ≃ TreeAction h M U)
    (v : TreeNode h) (hv : (v.1 : ℕ) + 1 = h)
    (active : ℕ → Fin (2 ^ h)) (coin : TreeNode h → Bool) (leafCoin : ℕ → Bool)
    (selected : Fin (2 ^ h) → Fin M) (q : ℕ → Fin N → ℝ)
    (hq : ∀ t < T, ∀ i, 0 ≤ q t i) :
    let i := e.symm (.inl (v, true))
    let w := v.child (by omega) true
    let u (t : ℕ) (j : Fin N) := treeBonusProb (active t) coin (leafCoin t) (selected (active t)) (e j)
    (∑ t ∈ Finset.range T, if w.active (active t) then q t i else 0) / (2 * treeHeight h)
      ≤ bestSwapGain T q u i := by
  intro i w u
  let a := e.symm (.inl (w, false))
  let b := e.symm (.inl (w, true))
  have hd : (v.1 : ℕ) < h := by omega
  have hw : (w.1 : ℕ) = h := hv
  have hH : 0 < treeHeight h := by unfold treeHeight; positivity
  have hed (t : ℕ) : w.active (active t) ↔ v.active (active t) ∧ v.mid ≤ (active t : ℕ) := by
    exact (v.child_active_iff hd (active t)).2
  have hdepth : (((v.1 : ℕ) : ℝ) + 1) = h := by exact_mod_cast hv
  have hEq : 1 - 2 * ((((v.1 : ℕ) : ℝ) + 1) / (2 * treeHeight h)) = 1 / treeHeight h := by
    rw [hdepth]
    field_simp
    simp [treeHeight]
  have hpoint (t : ℕ) (ht : t < T) :
      (if w.active (active t) then q t i / treeHeight h else 0) ≤
        q t i * (u t a - u t i) + q t i * (u t b - u t i) := by
    by_cases ha : w.active (active t)
    · have hp := (hed t).mp ha
      have hb : u t a + u t b = 1 := by
        simpa [u, a, b] using treeBonusProb_leaf_pair (U := U) (active t) w hw ha coin
          (leafCoin t) (selected (active t))
      have hi : u t i ≤ (((v.1 : ℕ) : ℝ) + 1) / (2 * treeHeight h) := by
        simp only [u, i, Equiv.apply_symm_apply, treeBonusProb, hp.1, if_true, hd.ne, if_false,
          not_lt_of_ge hp.2]
        split
        · exact le_rfl
        · positivity
      rw [if_pos ha]
      have hdiff : 1 / treeHeight h ≤ u t a + u t b - 2 * u t i := by
        rw [hb, ← hEq]
        linarith only [hi]
      have hm := mul_le_mul_of_nonneg_left hdiff (hq t ht i)
      rw [div_eq_mul_inv]
      norm_num [div_eq_mul_inv] at hm
      nlinarith only [hm]
    · rw [if_neg ha]
      have hcase : ¬ v.active (active t) ∨ (active t : ℕ) < v.mid := by
        rw [hed t] at ha
        by_cases hh : v.active (active t)
        · exact Or.inr (lt_of_not_ge fun hk => ha ⟨hh, hk⟩)
        · exact Or.inl hh
      have hi : u t i = 0 := by
        unfold u i
        simp only [Equiv.apply_symm_apply, treeBonusProb, hd.ne, if_false]
        rcases hcase with ho | hp
        · simp [ho]
        · simp [hp]
      have hab : u t a = 0 ∧ u t b = 0 := by simp [u, a, b, treeBonusProb, ha]
      simp [hi, hab.1, hab.2]
  have hs := Finset.sum_le_sum (s := Finset.range T) fun t ht => hpoint t (Finset.mem_range.mp ht)
  rw [Finset.sum_add_distrib] at hs
  change _ ≤ swapGain T q u i a + swapGain T q u i b at hs
  have he : (∑ t ∈ Finset.range T, if w.active (active t) then q t i / treeHeight h else 0) =
      (∑ t ∈ Finset.range T, if w.active (active t) then q t i else 0) / treeHeight h := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun t _ => by split <;> simp
  rw [he] at hs
  rw [show (2 * treeHeight h) = treeHeight h * 2 by ring, ← div_div]
  linarith only [hs, swapGain_le_best (T := T) q u i a, swapGain_le_best (T := T) q u i b]

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- The normalized observation uses the bonus transform exactly when the
independent threshold draw falls below the current bonus probability. -/
noncomputable def observationLaw (η u : ℝ) : Measure ℝ :=
  let Q : Measure ℝ := volume.restrict (Icc 0 1)
  ENNReal.ofReal (1 - u) • Q + ENNReal.ofReal u • Q.map (bonusTransform η)

theorem observationLaw_probability (η : ℝ) {u : ℝ} (hu : u ∈ Icc 0 1) :
    IsProbabilityMeasure (observationLaw η u) := by
  let Q : Measure ℝ := volume.restrict (Icc 0 1)
  have _ : IsProbabilityMeasure Q := ⟨by simp [Q, Real.volume_Icc]⟩
  have hm : Measurable (bonusTransform η) := by unfold bonusTransform; fun_prop
  have _ : IsProbabilityMeasure (Q.map (bonusTransform η)) := Measure.isProbabilityMeasure_map hm.aemeasurable
  refine ⟨?_⟩
  change (ENNReal.ofReal (1 - u) • Q + ENNReal.ofReal u • Q.map (bonusTransform η)) univ = 1
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr hu.2) hu.1]
  simp

theorem map_threshold_observation (η : ℝ) {u : ℝ} (hu : u ∈ Icc 0 1) :
    let Q : Measure ℝ := volume.restrict (Icc 0 1)
    let V : Measure ℝ := volume.restrict (Ico 0 1)
    (V.prod Q).map (fun p : ℝ × ℝ => if p.1 < u then bonusTransform η p.2 else p.2) =
      observationLaw η u := by
  intro Q V
  let f (p : ℝ × ℝ) := if p.1 < u then bonusTransform η p.2 else p.2
  have hb : Measurable (bonusTransform η) := by unfold bonusTransform; fun_prop
  have hm : Measurable f := Measurable.ite (measurableSet_lt measurable_fst measurable_const)
    (hb.comp measurable_snd) measurable_snd
  have _ : IsProbabilityMeasure Q := ⟨by simp [Q, Real.volume_Icc]⟩
  have hlow : V (Iio u) = ENNReal.ofReal u := by
    rw [show V = volume.restrict (Ico 0 1) from rfl, Measure.restrict_apply measurableSet_Iio]
    have he : Iio u ∩ Ico (0 : ℝ) 1 = Ico 0 u := by
      ext x
      simp only [mem_inter_iff, mem_Iio, mem_Ico]
      exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, h.2.trans_le hu.2⟩⟩
    rw [he, Real.volume_Ico, sub_zero]
  have hhigh : V (Ici u) = ENNReal.ofReal (1 - u) := by
    rw [show V = volume.restrict (Ico 0 1) from rfl, Measure.restrict_apply measurableSet_Ici]
    have he : Ici u ∩ Ico (0 : ℝ) 1 = Ico u 1 := by
      ext x
      simp only [mem_inter_iff, mem_Ici, mem_Ico]
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hu.1.trans h.1, h.2⟩⟩
    rw [he, Real.volume_Ico]
  ext s hs
  change ((V.prod Q).map f) s = _
  rw [Measure.map_apply hm hs, Measure.prod_apply (hm hs)]
  let F := (Iio u).indicator (fun _ : ℝ => Q (bonusTransform η ⁻¹' s))
  let G := (Ici u).indicator (fun _ : ℝ => Q s)
  have he (w : ℝ) : Q (Prod.mk w ⁻¹' (f ⁻¹' s)) = F w + G w := by
    by_cases hw : w < u
    · have heq : Prod.mk w ⁻¹' (f ⁻¹' s) = bonusTransform η ⁻¹' s := by
        ext z
        simp [f, hw]
      simp [heq, F, G, hw, not_le_of_gt hw]
    · have heq : Prod.mk w ⁻¹' (f ⁻¹' s) = s := by
        ext z
        simp [f, hw]
      simp [heq, F, G, hw, le_of_not_gt hw]
  rw [lintegral_congr he, lintegral_add_left (measurable_const.indicator measurableSet_Iio)]
  change (∫⁻ w, F w ∂V) + (∫⁻ w, G w ∂V) = _
  rw [lintegral_indicator_const measurableSet_Iio, lintegral_indicator_const measurableSet_Ici,
    hlow, hhigh]
  simp only [observationLaw, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply hb hs]
  change _ = ENNReal.ofReal (1 - u) * Q s + ENNReal.ofReal u * Q (bonusTransform η ⁻¹' s)
  ac_rfl

/-- The baseline observation kernel with every auxiliary bonus turned off. -/
noncomputable def treeAuxiliaryPeriod {h M U N : ℕ}
    (e : Fin N ≃ TreeAction h M U) (η : ℝ) (leaf : Fin (2 ^ h))
    (coin : TreeNode h → Bool) (leafCoin : ℕ → Bool) (dummy : Fin M)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N)
    (hm : ∀ t, Measurable (pick t)) : AuxiliaryPeriod N M := by
  let u (t : ℕ) (i : Fin N) : ℝ :=
    match e i with
    | .inr (.inl _) => 0
    | a => treeBonusProb leaf coin (leafCoin t) dummy a
  have hu (t : ℕ) (i : Fin N) : u t i ∈ Icc (0 : ℝ) 1 := by
    unfold u
    split
    · exact ⟨le_rfl, zero_le_one⟩
    · apply treeBonusProb_mem
  let kernel (t : ℕ) : Kernel (Fin N) ℝ :=
    Kernel.ofFunOfCountable (fun i => observationLaw η (u t i))
  have hk (t : ℕ) : IsMarkovKernel (kernel t) :=
    ⟨fun i => observationLaw_probability η (hu t i)⟩
  exact ⟨pick, hm, ⟨fun j => e.symm (.inr (.inl j)), by
      intro i j hij
      have he := e.symm.injective hij
      injection he with he
      injection he⟩,
    fun t => (kernel t).comap (pick t) (hm t),
    fun t => by
      let _ := hk t
      infer_instance⟩

/-- The selected-world kernel agrees with the actual tree reward law for
every action at every history. -/
theorem treeAuxiliaryPeriod_selected_step {h M U N : ℕ}
    (e : Fin N ≃ TreeAction h M U) (η : ℝ) (leaf : Fin (2 ^ h))
    (coin : TreeNode h → Bool) (leafCoin : ℕ → Bool) (dummy j : Fin M)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N)
    (hm : ∀ t, Measurable (pick t)) (t : ℕ) (x : FeedbackHistory t) :
    let A := treeAuxiliaryPeriod e η leaf coin leafCoin dummy pick hm
    let Q := volume.restrict (Icc (0 : ℝ) 1)
    (A.experiment j).step (Q.map (bonusTransform η)) t x =
      observationLaw η (treeBonusProb leaf coin (leafCoin t) j (e (pick t x))) := by
  classical
  intro A Q
  rw [AuxiliaryExperiment.step, Kernel.piecewise_apply]
  have hr : x ∈ (A.experiment j).query t ↔ e (pick t x) = .inr (.inl j) := by
    change pick t x = e.symm (.inr (.inl j)) ↔ _
    rw [Equiv.eq_symm_apply]
  simp only [hr]
  cases he : e (pick t x) with
  | inl a =>
    simp [he, A, treeAuxiliaryPeriod, AuxiliaryPeriod.experiment, Kernel.comap_apply,
      Kernel.ofFunOfCountable, treeBonusProb]
  | inr b =>
    cases b with
    | inl k =>
      by_cases hk : k = j
      · subst k
        simp [treeBonusProb, observationLaw, Q, Kernel.const_apply]
      · simp [he, hk, A, treeAuxiliaryPeriod, AuxiliaryPeriod.experiment, Kernel.comap_apply,
          Kernel.ofFunOfCountable, treeBonusProb, observationLaw]
    | inr k =>
      simp [he, A, treeAuxiliaryPeriod, AuxiliaryPeriod.experiment, Kernel.comap_apply,
        Kernel.ofFunOfCountable, treeBonusProb, observationLaw]

/-- The bound on the expected number of hits within a period of the actual
tree construction, for any fixed values of the tree and leaf coins. -/
theorem tree_period_average_hits {h M U N : ℕ}
    (e : Fin N ≃ TreeAction h M U) (η : ℝ) (hη : 0 ≤ η) (hη₁ : η < 1)
    (leaf : Fin (2 ^ h)) (coin : TreeNode h → Bool) (leafCoin : ℕ → Bool) (dummy : Fin M)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (hm : ∀ t, Measurable (pick t))
    (r : ℕ) :
    let A := treeAuxiliaryPeriod e η leaf coin leafCoin dummy pick hm
    let Q := volume.restrict (Icc (0 : ℝ) 1)
    let Q' := Q.map (bonusTransform η)
    (∑ j : Fin M, ∑ i : Fin r, ((A.experiment j).law Q' r).real ((A.experiment j).hit r i)) / M
      ≤ (r : ℝ) / M + η * r * Real.sqrt ((r : ℝ) / (6 * M)) := by
  intro A Q Q'
  refine A.average_bonus_hits_le (Nat.zero_lt_of_lt dummy.isLt) r hη hη₁ ?_
  intro t x j hx
  have hx' : pick t x = e.symm (.inr (.inl j)) := hx
  have he := congrArg e hx'
  simp only [Equiv.apply_symm_apply] at he
  change (Kernel.ofFunOfCountable (fun i =>
    observationLaw η (match e i with
      | .inr (.inl _) => 0
      | a => treeBonusProb leaf coin (leafCoin t) dummy a))) (pick t x) = Q
  simp [Kernel.ofFunOfCountable, he, observationLaw, Q]

/-- A round uses one common base draw and an independent threshold draw
for each action. This is the normalized reward for one action. -/
noncomputable def observedReward {N : ℕ} (η u : ℝ) (i : Fin N)
    (p : ℝ × (Fin N → ℝ)) : ℝ :=
  if p.2 i < u then bonusTransform η p.1 else p.1

theorem measurable_observedReward {N : ℕ} (η u : ℝ) (i : Fin N) :
    Measurable (observedReward η u i) := by
  have hm : Measurable (bonusTransform η) := by unfold bonusTransform; fun_prop
  exact Measurable.ite (measurableSet_lt ((measurable_pi_apply i).comp measurable_snd) measurable_const)
    (hm.comp measurable_fst) measurable_fst

theorem map_observedReward {N : ℕ} (η : ℝ) {u : ℝ} (hu : u ∈ Icc 0 1) (i : Fin N) :
    let Q : Measure ℝ := volume.restrict (Icc 0 1)
    let V : Measure ℝ := volume.restrict (Ico 0 1)
    let tape := Q.prod (Measure.pi fun _ : Fin N => V)
    tape.map (observedReward η u i) = observationLaw η u := by
  intro Q V tape
  have _ : IsProbabilityMeasure Q := ⟨by simp [Q, Real.volume_Icc]⟩
  have _ : IsProbabilityMeasure V := ⟨by simp [V, Real.volume_Ico]⟩
  let τ : Measure (Fin N → ℝ) := Measure.pi fun _ : Fin N => V
  let get (r : Fin N → ℝ) := r i
  have hg : Measurable get := measurable_pi_apply i
  have hmap : τ.map get = V := (measurePreserving_eval (fun _ : Fin N => V) i).map_eq
  have hp : (Q.prod τ).map (Prod.map id get) = Q.prod V := by
    rw [← Measure.map_prod_map _ _ measurable_id hg, Measure.map_id, hmap]
  let f (p : ℝ × ℝ) := if p.1 < u then bonusTransform η p.2 else p.2
  have hb : Measurable (bonusTransform η) := by unfold bonusTransform; fun_prop
  have hf : Measurable f := Measurable.ite (measurableSet_lt measurable_fst measurable_const)
    (hb.comp measurable_snd) measurable_snd
  change (Q.prod τ).map ((f ∘ Prod.swap) ∘ Prod.map id get) = _
  rw [← Measure.map_map (hf.comp measurable_swap) (measurable_id.prodMap hg), hp,
    ← Measure.map_map hf measurable_swap, Measure.prod_swap]
  exact map_threshold_observation η hu

/-- The next transcript is obtained by appending the observation from an
independent draw. This describes the same law as the observation kernel. -/
theorem map_product_append {A B H Y : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace H] [MeasurableSpace Y] (μ : Measure A) (ν : Measure B)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (past : A → H) (hp : Measurable past)
    (observe : H × B → Y) (ho : Measurable observe)
    (κ : Kernel H Y) [IsMarkovKernel κ]
    (hk : ∀ x, κ x = ν.map (fun b => observe (x, b))) :
    (μ.prod ν).map (fun x : A × B => (past x.1, observe (past x.1, x.2))) =
      μ.map past ⊗ₘ κ := by
  let f (x : A × B) := (past x.1, observe (past x.1, x.2))
  have hm : Measurable f :=
    (hp.comp measurable_fst).prodMk (ho.comp ((hp.comp measurable_fst).prodMk measurable_snd))
  ext s hs
  change ((μ.prod ν).map f) s = _
  rw [Measure.map_apply hm hs, Measure.prod_apply (hm hs), Measure.compProd_apply hs,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hp]
  apply lintegral_congr
  intro a
  rw [hk]
  have hx : Measurable (fun b => observe (past a, b)) := ho.comp measurable_prodMk_left
  rw [Measure.map_apply hx (measurable_prodMk_left hs)]
  rfl

noncomputable def observationOfHistory {N t : ℕ} (η : ℝ) (u : Fin N → ℝ)
    (pick : FeedbackHistory t → Fin N) (p : FeedbackHistory t × (ℝ × (Fin N → ℝ))) : ℝ :=
  observedReward η (u (pick p.1)) (pick p.1) p.2

theorem measurable_observationOfHistory {N t : ℕ} (η : ℝ) (u : Fin N → ℝ)
    (pick : FeedbackHistory t → Fin N) (hm : Measurable pick) :
    Measurable (observationOfHistory η u pick) :=
  measurable_select (hm.comp measurable_fst)
    fun i => (measurable_observedReward η (u i) i).comp measurable_snd

noncomputable def transcriptFromTape {N : ℕ} (η : ℝ) (u : ℕ → Fin N → ℝ)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) :
    (t : ℕ) → RewardTape N t → FeedbackHistory t
  | 0, _ => ()
  | t + 1, p =>
    let past := transcriptFromTape η u pick t p.1
    (past, observationOfHistory η (u t) (pick t) (past, p.2))

theorem measurable_transcriptFromTape {N : ℕ} (η : ℝ) (u : ℕ → Fin N → ℝ)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (hm : ∀ t, Measurable (pick t))
    (r : ℕ) : Measurable (transcriptFromTape η u pick r) := by
  induction r with
  | zero => exact measurable_const
  | succ r ih =>
    change Measurable (fun p : RewardTape N r × (ℝ × (Fin N → ℝ)) =>
      (transcriptFromTape η u pick r p.1,
        observationOfHistory η (u r) (pick r) (transcriptFromTape η u pick r p.1, p.2)))
    have hp : Measurable (fun p : RewardTape N r × (ℝ × (Fin N → ℝ)) =>
        transcriptFromTape η u pick r p.1) := ih.comp measurable_fst
    exact hp.prodMk ((measurable_observationOfHistory η (u r) (pick r) (hm r)).comp
      (hp.prodMk measurable_snd))

set_option maxHeartbeats 850000 in
/-- The product law of the complete reward tape induces the observation
kernel law in each selected world of the lower bound. -/
theorem treeAuxiliaryPeriod_law_eq_map {h M U N : ℕ}
    (e : Fin N ≃ TreeAction h M U) (η : ℝ) (leaf : Fin (2 ^ h))
    (coin : TreeNode h → Bool) (leafCoin : ℕ → Bool) (dummy j : Fin M)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N)
    (hm : ∀ t, Measurable (pick t)) (r : ℕ) :
    let A := treeAuxiliaryPeriod e η leaf coin leafCoin dummy pick hm
    let Q := volume.restrict (Icc (0 : ℝ) 1)
    let u (t : ℕ) (i : Fin N) := treeBonusProb leaf coin (leafCoin t) j (e i)
    (rewardTapeLaw N r).map (transcriptFromTape η u pick r) =
      (A.experiment j).law (Q.map (bonusTransform η)) r := by
  intro A Q u
  have _ : IsProbabilityMeasure Q := ⟨by simp [Q, Real.volume_Icc]⟩
  have hη : Measurable (bonusTransform η) := by unfold bonusTransform; fun_prop
  have _ : IsProbabilityMeasure (Q.map (bonusTransform η)) := Measure.isProbabilityMeasure_map hη.aemeasurable
  let X := A.experiment j
  induction r with
  | zero =>
    change (Measure.dirac ((): Unit)).map (fun _ : Unit => ()) = Measure.dirac ()
    exact Measure.map_dirac' (measurable_const : Measurable (fun _ : Unit => ())) ()
  | succ r ih =>
    let κ := X.step (Q.map (bonusTransform η)) r
    have hk (x : FeedbackHistory r) :
        κ x = (roundDrawLaw N).map (fun b => observationOfHistory η (u r) (pick r) (x, b)) := by
      have hu := treeBonusProb_mem (U := U) leaf coin (leafCoin r) j (e (pick r x))
      exact (treeAuxiliaryPeriod_selected_step e η leaf coin leafCoin dummy j pick hm r x).trans
        (map_observedReward η hu (pick r x)).symm
    have hnext := map_product_append (rewardTapeLaw N r) (roundDrawLaw N)
      (transcriptFromTape η u pick r) (measurable_transcriptFromTape η u pick hm r)
      (observationOfHistory η (u r) (pick r)) (measurable_observationOfHistory η (u r) (pick r) (hm r))
      κ hk
    rw [ih] at hnext
    exact hnext

open scoped Interval in
/-- The normalized observation has mean one half plus ηu/6. -/
theorem integral_observationLaw (η : ℝ) {u : ℝ} (hu : u ∈ Icc 0 1) :
    (∫ x, x ∂observationLaw η u) = 1 / 2 + η * u / 6 := by
  let Q : Measure ℝ := volume.restrict (Icc 0 1)
  have hm : Measurable (bonusTransform η) := by unfold bonusTransform; fun_prop
  have hrest : Q = volume.restrict (Ioc 0 1) := (Measure.restrict_congr_set Ioc_ae_eq_Icc).symm
  have hbase : IntervalIntegrable (fun x : ℝ => x) volume 0 1 :=
    continuous_id.intervalIntegrable _ _
  have hquad : IntervalIntegrable (fun x : ℝ => x ^ 2) volume 0 1 :=
    (continuous_id.pow 2).intervalIntegrable _ _
  have hb : Continuous (bonusTransform η) := by unfold bonusTransform; fun_prop
  have ht : IntervalIntegrable (bonusTransform η) volume 0 1 := hb.intervalIntegrable _ _
  have hi : Integrable (fun x : ℝ => x) Q := by rw [hrest]; exact hbase.1
  have ht' : Integrable (bonusTransform η) Q := by rw [hrest]; exact ht.1
  have hmi : Integrable (fun x : ℝ => x) (Q.map (bonusTransform η)) :=
    (integrable_map_measure continuous_id.stronglyMeasurable.aestronglyMeasurable hm.aemeasurable).mpr ht'
  have hbaseval : (∫ x, x ∂Q) = (1 / 2 : ℝ) := by
    rw [hrest, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_id]
    norm_num
  have htrans : (∫ x, x ∂Q.map (bonusTransform η)) = 1 / 2 + η / 6 := by
    rw [integral_map (f := fun x : ℝ => x) hm.aemeasurable continuous_id.stronglyMeasurable.aestronglyMeasurable,
      hrest, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    rw [show bonusTransform η = fun x => x + η * (x - x ^ 2) by
      funext x; unfold bonusTransform; ring]
    rw [intervalIntegral.integral_add hbase ((hbase.sub hquad).const_mul η),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hbase hquad,
      integral_id, integral_pow]
    norm_num
    ring
  change (∫ x, x ∂(ENNReal.ofReal (1 - u) • Q +
    ENNReal.ofReal u • Q.map (bonusTransform η))) = _
  rw [integral_add_measure (hi.smul_measure ENNReal.ofReal_ne_top) (hmi.smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, hbaseval, htrans]
  simp only [ENNReal.toReal_ofReal (sub_nonneg.mpr hu.2), ENNReal.toReal_ofReal hu.1, smul_eq_mul]
  ring

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open MeasureTheory Set

@[simp] theorem rewardTapePrefix_refl (N r : ℕ) :
    rewardTapePrefix N (le_refl r) = id := by simp [rewardTapePrefix]

@[simp] theorem rewardTapePrefix_succ (N : ℕ) {r t : ℕ} (h : r ≤ t) :
    rewardTapePrefix N (Nat.le_succ_of_le h) = rewardTapePrefix N h ∘ Prod.fst := by
  unfold rewardTapePrefix
  exact Nat.leRec_succ _ _ h

theorem measurable_rewardTapePrefix (N : ℕ) {r t : ℕ} (h : r ≤ t) :
    Measurable (rewardTapePrefix N h) := by
  induction h with
  | refl => rw [rewardTapePrefix_refl]; exact measurable_id
  | step h ih => rw [rewardTapePrefix_succ N h]; exact ih.comp measurable_fst

theorem rewardTapePrefix_comp (N : ℕ) {r s t : ℕ} (hrs : r ≤ s) (hst : s ≤ t) :
    rewardTapePrefix N hrs ∘ rewardTapePrefix N hst = rewardTapePrefix N (hrs.trans hst) := by
  induction hst with
  | refl => simp
  | step hs ih =>
    rw [rewardTapePrefix_succ N hs, rewardTapePrefix_succ N (hrs.trans hs)]
    funext tape
    exact congrFun ih tape.1

theorem rewardTapePrefix_map (N : ℕ) {r t : ℕ} (h : r ≤ t) :
    (rewardTapeLaw N t).map (rewardTapePrefix N h) = rewardTapeLaw N r := by
  induction h with
  | refl => rw [rewardTapePrefix_refl, Measure.map_id]
  | step h ih =>
    rw [rewardTapePrefix_succ N h]
    change ((rewardTapeLaw N _).prod (roundDrawLaw N)).map
      (rewardTapePrefix N h ∘ Prod.fst) = _
    rw [← Measure.map_map (measurable_rewardTapePrefix N h) measurable_fst, Measure.map_fst_prod,
      measure_univ, one_smul, ih]

/-- Information supplied by the reward tape before each round. Past the
horizon the information stays the full tape. -/
def rewardTapeFiltration (N T : ℕ) : Filtration ℕ (rewardTapeMeasurable N T) where
  seq t := MeasurableSpace.comap (rewardTapePrefix N (min_le_right t T))
    (rewardTapeMeasurable N (min t T))
  mono' := by
    intro r s hrs
    have h := min_le_min hrs (le_refl T)
    change MeasurableSpace.comap (rewardTapePrefix N (min_le_right r T))
        (rewardTapeMeasurable N (min r T)) ≤
      MeasurableSpace.comap (rewardTapePrefix N (min_le_right s T))
        (rewardTapeMeasurable N (min s T))
    rw [← rewardTapePrefix_comp N h (min_le_right s T), ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono ((measurable_rewardTapePrefix N h).comap_le)
  le' := fun t => (measurable_rewardTapePrefix N (min_le_right t T)).comap_le

/-- Conditional expectation over a fresh independent draw, with the past
as the first coordinate of the product sample space. -/
theorem condExp_product_past {A B : Type*} [mA : MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : A × B → ℝ) (hf : Measurable f) (hi : Integrable f (μ.prod ν)) :
    condExp (mA.comap (Prod.fst : A × B → A)) (μ.prod ν) f =ᵐ[μ.prod ν]
      fun p => ∫ b, f (p.1, b) ∂ν := by
  let g (a : A) := ∫ b, f (a, b) ∂ν
  have hm : Measurable g := hf.stronglyMeasurable.integral_prod_right'.measurable
  have hg : Integrable g μ := hi.integral_prod_left
  have hfst : Measurable[mA.comap (Prod.fst : A × B → A)] (Prod.fst : A × B → A) :=
    measurable_iff_comap_le.mpr le_rfl
  have hGi : Integrable (g ∘ Prod.fst) (μ.prod ν) := by
    have he : (μ.prod ν).map Prod.fst = μ := by rw [Measure.map_fst_prod, measure_univ, one_smul]
    have he' : Integrable g ((μ.prod ν).map Prod.fst) := by rw [he]; exact hg
    exact (integrable_map_measure hm.aestronglyMeasurable measurable_fst.aemeasurable).mp he'
  symm
  refine ae_eq_condExp_of_forall_setIntegral_eq measurable_fst.comap_le hi
    (fun _ _ _ => hGi.integrableOn) ?_ (hm.comp hfst).aestronglyMeasurable
  rintro s ⟨t, ht, rfl⟩ _
  have hset : (Prod.fst : A × B → A) ⁻¹' t = t ×ˢ (univ : Set B) := by ext p; simp
  change (∫ p in Prod.fst ⁻¹' t, (g ∘ Prod.fst) p ∂μ.prod ν) = ∫ p in Prod.fst ⁻¹' t, f p ∂μ.prod ν
  rw [hset, setIntegral_prod _ hGi.integrableOn, setIntegral_prod _ hi.integrableOn]
  simp only [Measure.restrict_univ]
  congr 1
  funext a
  change (∫ _ : B, g a ∂ν) = g a
  simp

set_option linter.style.haveILetI false in
/-- A conditional expectation can be pulled back through a measure-preserving
map when the information is pulled back through the same map. -/
theorem condExp_pullback {A B : Type*} [mA : MeasurableSpace A] [mB : MeasurableSpace B]
    (μ : Measure A) [IsProbabilityMeasure μ] (ν : Measure B) [IsProbabilityMeasure ν]
    (p : A → B) (hp : MeasurePreserving p μ ν)
    (m : MeasurableSpace B) (hm : m ≤ mB)
    (f : B → ℝ) (hf : Integrable f ν) :
    μ[f ∘ p | m.comap p] =ᵐ[μ] (ν[f | m]) ∘ p := by
  letI : MeasurableSpace B := mB
  let g := ν[f | m]
  have hmg : StronglyMeasurable[m] g := stronglyMeasurable_condExp
  have hgi : Integrable g ν := integrable_condExp
  have hmapped {k : B → ℝ} (hk : Integrable k ν) : Integrable k (μ.map p) := by
    rw [hp.map_eq]
    exact hk
  have hgp : Integrable (g ∘ p) μ := (hmapped hgi).comp_measurable hp.measurable
  have hfp : Integrable (f ∘ p) μ := (hmapped hf).comp_measurable hp.measurable
  have hmp : m.comap p ≤ mA := (MeasurableSpace.comap_mono hm).trans hp.measurable.comap_le
  have hpg : Measurable[m.comap p, m] p := measurable_iff_comap_le.mpr le_rfl
  symm
  refine ae_eq_condExp_of_forall_setIntegral_eq hmp hfp
    (fun _ _ _ => hgp.integrableOn) ?_ (hmg.comp_measurable hpg).aestronglyMeasurable
  rintro _ ⟨s, hs, rfl⟩ _
  have hs' : MeasurableSet s := hm s hs
  have hg' : AEStronglyMeasurable g (μ.map p) := hp.map_eq ▸ hgi.aestronglyMeasurable
  have hf' : AEStronglyMeasurable f (μ.map p) := hp.map_eq ▸ hf.aestronglyMeasurable
  change (∫ x in p ⁻¹' s, g (p x) ∂μ) = ∫ x in p ⁻¹' s, f (p x) ∂μ
  rw [← setIntegral_map hs' hg' hp.measurable.aemeasurable,
      ← setIntegral_map hs' hf' hp.measurable.aemeasurable, hp.map_eq]
  exact setIntegral_condExp hm hf hs

private theorem comap_prefix_congr (N T : ℕ) {r s : ℕ} (h : r = s) (hr : r ≤ T) (hs : s ≤ T) :
    (rewardTapeMeasurable N r).comap (rewardTapePrefix N hr) =
      (rewardTapeMeasurable N s).comap (rewardTapePrefix N hs) := by
  subst s
  rfl

/-- On the full tape, the information at round t is the pullback of
the past coordinate of the tape truncated just after round t. -/
theorem rewardTapeFiltration_eq_comap {N T t : ℕ} (ht : t < T) :
    rewardTapeFiltration N T t =
      ((rewardTapeMeasurable N t).comap
        (Prod.fst : RewardTape N (t + 1) → RewardTape N t)).comap
        (rewardTapePrefix N (Nat.succ_le_of_lt ht)) := by
  have he : rewardTapeFiltration N T t =
      (rewardTapeMeasurable N t).comap (rewardTapePrefix N ht.le) := by
    change (rewardTapeMeasurable N (min t T)).comap
      (rewardTapePrefix N (min_le_right t T)) = _
    exact comap_prefix_congr N T (min_eq_left ht.le) _ _
  rw [he]
  let fst : RewardTape N (t + 1) → RewardTape N t := Prod.fst
  have hf : rewardTapePrefix N (Nat.le_succ t) = fst := by
    rw [rewardTapePrefix_succ N (le_refl t), rewardTapePrefix_refl, Function.id_comp]
  have hc := rewardTapePrefix_comp N (Nat.le_succ t) (Nat.succ_le_of_lt ht)
  rw [hf] at hc
  calc
    _ = (rewardTapeMeasurable N t).comap (fst ∘ rewardTapePrefix N (Nat.succ_le_of_lt ht)) :=
      congrArg (fun (g : RewardTape N T → RewardTape N t) =>
        (rewardTapeMeasurable N t).comap g) hc.symm
    _ = _ := MeasurableSpace.comap_comp.symm

/-- The one-step conditional mean on the full reward tape is the integral
over that step's independent draw, with the observed past held fixed. -/
theorem condExp_rewardTape_step {N T t : ℕ} (ht : t < T)
    (f : RewardTape N (t + 1) → ℝ) (hf : Measurable f)
    (hi : Integrable f (rewardTapeLaw N (t + 1))) :
    let pre := rewardTapePrefix N (Nat.succ_le_of_lt ht)
    (rewardTapeLaw N T)[f ∘ pre | rewardTapeFiltration N T t] =ᵐ[rewardTapeLaw N T]
      fun x => ∫ d, f ((pre x).1, d) ∂roundDrawLaw N := by
  intro pre
  let μ := rewardTapeLaw N T
  let ν := rewardTapeLaw N (t + 1)
  let m := (rewardTapeMeasurable N t).comap
    (Prod.fst : RewardTape N (t + 1) → RewardTape N t)
  have hp : MeasurePreserving pre μ ν :=
    ⟨measurable_rewardTapePrefix N _, rewardTapePrefix_map N _⟩
  have hm : m ≤ rewardTapeMeasurable N (t + 1) := measurable_fst.comap_le
  rw [rewardTapeFiltration_eq_comap ht]
  have h := condExp_pullback μ ν pre hp m hm f hi
  refine h.trans ?_
  have hv := condExp_product_past (rewardTapeLaw N t) (roundDrawLaw N) f hf hi
  change (ν[f | m]) =ᵐ[ν] (fun p => ∫ d, f (p.1, d) ∂roundDrawLaw N) at hv
  refine ae_of_ae_map hp.aemeasurable
    (p := fun p => (ν[f | m]) p = ∫ d, f (p.1, d) ∂roundDrawLaw N) ?_
  rw [hp.map_eq]
  exact hv

/-- Every function of the truncated tape through round t is measurable
at t + 1 in the full tape filtration. -/
theorem measurable_rewardTape_step {N T t : ℕ} (ht : t < T)
    (f : RewardTape N (t + 1) → ℝ) (hf : Measurable f) :
    Measurable[rewardTapeFiltration N T (t + 1)]
      (f ∘ rewardTapePrefix N (Nat.succ_le_of_lt ht)) := by
  have he : rewardTapeFiltration N T (t + 1) =
      (rewardTapeMeasurable N (t + 1)).comap (rewardTapePrefix N (Nat.succ_le_of_lt ht)) := by
    change (rewardTapeMeasurable N (min (t + 1) T)).comap
      (rewardTapePrefix N (min_le_right (t + 1) T)) = _
    exact comap_prefix_congr N T (min_eq_left (Nat.succ_le_of_lt ht)) _ _
  rw [he]
  exact hf.comp (measurable_iff_comap_le.mpr le_rfl)

open scoped ENNReal

theorem measurable_supportedBase : Measurable fun x => (supportedBase x : ℝ) := by
  have he : (fun x => (supportedBase x : ℝ)) = fun x => if x ∈ Icc (0 : ℝ) 1 then x else 0 := by
    funext x
    by_cases hx : x ∈ Icc (0 : ℝ) 1 <;> simp [supportedBase, hx]
  rw [he]
  exact Measurable.ite measurableSet_Icc measurable_id measurable_const

theorem measurable_supportedThreshold : Measurable fun x => (supportedThreshold x : ℝ) := by
  have he : (fun x => (supportedThreshold x : ℝ)) = fun x => if x ∈ Ico (0 : ℝ) 1 then x else 0 := by
    funext x
    by_cases hx : x ∈ Ico (0 : ℝ) 1 <;> simp [supportedThreshold, hx]
  rw [he]
  exact Measurable.ite measurableSet_Ico measurable_id measurable_const

theorem measurable_boundedRoundReward {N : ℕ} (η u : ℝ) (i : Fin N) :
    Measurable (boundedRoundReward η u i) := by
  let z (d : ℝ × (Fin N → ℝ)) : ℝ := supportedBase d.1
  have hz : Measurable z := measurable_supportedBase.comp measurable_fst
  have hth := measurable_supportedThreshold.comp ((measurable_pi_apply i).comp
    (measurable_snd : Measurable (Prod.snd : ℝ × (Fin N → ℝ) → (Fin N → ℝ))))
  unfold boundedRoundReward bonusReward
  simp only [decide_eq_true_eq]
  exact (measurable_const.add (hz.div_const _)).add
    (((hz.const_mul _).mul (measurable_const.sub hz)).mul
      (Measurable.ite (measurableSet_lt hth measurable_const) measurable_const measurable_const))

/-- Clipping on the null complement of the support does not change the mean. -/
theorem integral_boundedRoundReward {N : ℕ} (η : ℝ) {u : ℝ} (hu : u ∈ Icc 0 1) (i : Fin N)
    (hη : 0 ≤ η) (hη₁ : η ≤ 1) :
    (∫ d, boundedRoundReward η u i d ∂roundDrawLaw N) = 3 / 16 + η * u / 48 := by
  let Q : Measure ℝ := volume.restrict (Icc 0 1)
  let V : Measure ℝ := volume.restrict (Ico 0 1)
  have _ : IsProbabilityMeasure Q := ⟨by simp [Q, Real.volume_Icc]⟩
  have _ : IsProbabilityMeasure V := ⟨by simp [V, Real.volume_Ico]⟩
  let τ : Measure (Fin N → ℝ) := Measure.pi fun _ : Fin N => V
  have hdraw : (roundDrawLaw N).map Prod.fst = Q := by
    change (Q.prod τ).map Prod.fst = Q
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hthreshold : (roundDrawLaw N).map (fun d => d.2 i) = V := by
    change (Q.prod τ).map ((fun r => r i) ∘ Prod.snd) = V
    rw [← Measure.map_map (measurable_pi_apply i) measurable_snd, Measure.map_snd_prod,
      measure_univ, one_smul, (measurePreserving_eval (fun _ : Fin N => V) i).map_eq]
  have hbase : ∀ᵐ d ∂roundDrawLaw N, d.1 ∈ Icc (0 : ℝ) 1 := by
    apply ae_of_ae_map measurable_fst.aemeasurable
    rw [hdraw]
    exact ae_restrict_mem measurableSet_Icc
  have hth : ∀ᵐ d ∂roundDrawLaw N, d.2 i ∈ Ico (0 : ℝ) 1 := by
    apply ae_of_ae_map ((measurable_pi_apply i).comp measurable_snd).aemeasurable
    change ∀ᵐ x ∂(roundDrawLaw N).map (fun d => d.2 i), x ∈ Ico (0 : ℝ) 1
    rw [hthreshold]
    exact ae_restrict_mem measurableSet_Ico
  have heq : boundedRoundReward η u i =ᵐ[roundDrawLaw N]
      fun d => 1 / 8 + observedReward η u i d / 8 := by
    filter_upwards [hbase, hth] with d hz hd
    unfold boundedRoundReward bonusReward observedReward bonusTransform
    simp only [supportedBase, supportedThreshold, dif_pos hz, dif_pos hd, decide_eq_true_eq]
    split <;> ring
  have hb : Integrable (observedReward η u i) (roundDrawLaw N) := by
    refine Integrable.of_bound ((measurable_observedReward η u i).aestronglyMeasurable) 1 ?_
    filter_upwards [hbase] with d hz
    unfold observedReward bonusTransform
    rcases hz with ⟨hz0,hz1⟩
    rw [Real.norm_eq_abs, abs_le]
    by_cases hh : d.2 i < u
    · rw [if_pos hh]
      have hn : 0 ≤ η * d.1 * (1 - d.1) := by positivity
      have hp : 0 ≤ (1 - η * d.1) * (1 - d.1) :=
        mul_nonneg (sub_nonneg.mpr (mul_le_one₀ hη₁ hz0 hz1)) (sub_nonneg.mpr hz1)
      constructor <;> nlinarith
    · rw [if_neg hh]
      constructor <;> linarith
  have hi :
      (∫ d, observedReward η u i d ∂roundDrawLaw N) = 1 / 2 + η * u / 6 := by
    have hmap : (roundDrawLaw N).map (observedReward η u i) = observationLaw η u :=
      map_observedReward η hu i
    have he := integral_map (measurable_observedReward η u i).aemeasurable
      (measurable_id.aestronglyMeasurable :
        AEStronglyMeasurable (id : ℝ → ℝ) ((roundDrawLaw N).map (observedReward η u i)))
    rw [hmap] at he
    exact he.symm.trans (integral_observationLaw η hu)
  rw [integral_congr_ae heq, integral_add (integrable_const _) (hb.div_const _),
    integral_const, probReal_univ, one_smul, integral_div, hi]
  ring

theorem boundedRoundReward_mem {N : ℕ} {η : ℝ} (hη : 0 ≤ η) (hη₁ : η ≤ 1)
    (u : ℝ) (i : Fin N) (d : ℝ × (Fin N → ℝ)) :
    boundedRoundReward η u i d ∈ Icc (0 : ℝ) 1 := by
  let z := (supportedBase d.1 : ℝ)
  have hz₀ : 0 ≤ z := (supportedBase d.1).property.1
  have hz₁ : z ≤ 1 := (supportedBase d.1).property.2
  have hsub : 0 ≤ 1 - z := sub_nonneg.mpr hz₁
  have hprod : 0 ≤ η / 8 * z * (1 - z) := by positivity
  have hηz : η / 8 * z ≤ 1 / 8 := by
    calc
      _ ≤ (1 / 8 : ℝ) * z := mul_le_mul_of_nonneg_right (by linarith) hz₀
      _ ≤ 1 / 8 := mul_le_of_le_one_right (by positivity) hz₁
  have hp : η / 8 * z * (1 - z) ≤ 1 / 8 := by
    exact (mul_le_mul_of_nonneg_right hηz hsub).trans
      (mul_le_of_le_one_right (by positivity) (by linarith))
  unfold boundedRoundReward bonusReward
  change (1 / 8 + z / 8 + η / 8 * z * (1 - z) * (if _ then 1 else 0) : ℝ) ∈ Icc 0 1
  split <;> simp only [mul_one, mul_zero] <;> exact ⟨by linarith, by linarith⟩

/-- A policy's one-round swap gain minus its predicted gain. The prediction
uses the bonus probabilities, and the policy depends only on the past. -/
noncomputable def centeredTreeStep {N t : ℕ} (η : ℝ) (u : Fin N → ℝ)
    (pick : RewardTape N t → Fin N) (i j : Fin N) (x : RewardTape N (t + 1)) : ℝ :=
  if pick x.1 = i then
    boundedRoundReward η (u j) j x.2 - boundedRoundReward η (u i) i x.2 -
      (η / 48) * (u j - u i)
  else 0

theorem measurable_centeredTreeStep {N t : ℕ} (η : ℝ) (u : Fin N → ℝ)
    (pick : RewardTape N t → Fin N) (hp : Measurable pick) (i j : Fin N) :
    Measurable (centeredTreeStep η u pick i j) := by
  exact Measurable.ite (measurableSet_eq_fun (hp.comp measurable_fst) measurable_const)
    ((((measurable_boundedRoundReward η (u j) j).comp measurable_snd).sub
      ((measurable_boundedRoundReward η (u i) i).comp measurable_snd)).sub measurable_const)
    measurable_const

theorem abs_centeredTreeStep {N t : ℕ} {η : ℝ} (hη : 0 ≤ η) (hη₁ : η ≤ 1)
    (u : Fin N → ℝ) (hu : ∀ i, u i ∈ Icc 0 1)
    (pick : RewardTape N t → Fin N) (i j : Fin N) (x : RewardTape N (t + 1)) :
    |centeredTreeStep η u pick i j x| ≤ 2 := by
  unfold centeredTreeStep
  split
  · obtain ⟨hi₀, hi₁⟩ := boundedRoundReward_mem hη hη₁ (u i) i x.2
    obtain ⟨hj₀, hj₁⟩ := boundedRoundReward_mem hη hη₁ (u j) j x.2
    have h₀ : (-1 : ℝ) ≤ u j - u i := by linarith only [(hu j).1, (hu i).2]
    have h₁ : u j - u i ≤ 1 := by linarith only [(hu j).2, (hu i).1]
    have hη' : 0 ≤ η / 48 := by positivity
    rw [abs_le]
    constructor
    · linarith only [mul_le_mul_of_nonneg_left h₁ hη', hj₀, hi₁, hη₁]
    · linarith only [mul_le_mul_of_nonneg_left h₀ hη', hj₁, hi₀, hη₁]
  · norm_num

/-- Realized swap gain minus predicted gain is a martingale difference
for the reward tape of the tree construction. -/
theorem condExp_centeredTreeStep {N T t : ℕ} (ht : t < T) {η : ℝ}
    (hη : 0 ≤ η) (hη₁ : η ≤ 1) (u : Fin N → ℝ) (hu : ∀ i, u i ∈ Icc 0 1)
    (pick : RewardTape N t → Fin N) (hp : Measurable pick) (i j : Fin N) :
    let d := centeredTreeStep η u pick i j ∘ rewardTapePrefix N (Nat.succ_le_of_lt ht)
    (rewardTapeLaw N T)[d | rewardTapeFiltration N T t] =ᵐ[rewardTapeLaw N T] 0 := by
  intro d
  let f := centeredTreeStep η u pick i j
  have hm := measurable_centeredTreeStep η u pick hp i j
  have hi : Integrable f (rewardTapeLaw N (t + 1)) := by
    refine Integrable.of_bound hm.aestronglyMeasurable 2 (Filter.Eventually.of_forall fun x => ?_)
    exact Real.norm_eq_abs _ ▸ abs_centeredTreeStep hη hη₁ u hu pick i j x
  refine (condExp_rewardTape_step ht f hm hi).trans ?_
  refine Filter.Eventually.of_forall fun x => ?_
  let p := rewardTapePrefix N (Nat.succ_le_of_lt ht) x
  change (∫ w, f (p.1, w) ∂roundDrawLaw N) = 0
  by_cases ha : pick p.1 = i
  · have hr (k : Fin N) : Integrable (boundedRoundReward η (u k) k) (roundDrawLaw N) := by
      refine Integrable.of_bound (measurable_boundedRoundReward η (u k) k).aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun w => ?_)
      obtain ⟨hl, hh⟩ := boundedRoundReward_mem hη hη₁ (u k) k w
      rwa [Real.norm_eq_abs, abs_of_nonneg hl]
    simp only [f, centeredTreeStep, ha, if_true]
    let ν := roundDrawLaw N
    let a := η / 48 * (u j - u i)
    calc
      _ = (∫ w, boundedRoundReward η (u j) j w - boundedRoundReward η (u i) i w ∂ν) -
          (∫ _w, a ∂ν) := integral_sub ((hr j).sub (hr i)) (integrable_const a)
      _ = 0 := by
        change (∫ w, boundedRoundReward η (u j) j w - boundedRoundReward η (u i) i w ∂roundDrawLaw N) -
          (∫ _w, a ∂roundDrawLaw N) = 0
        rw [integral_sub (hr j) (hr i), integral_boundedRoundReward η (hu j) j hη hη₁,
          integral_boundedRoundReward η (hu i) i hη hη₁, integral_const, probReal_univ, one_smul]
        dsimp [a]
        ring
  · simp [f, centeredTreeStep, ha]

/-- The common base reward cancels in a swap comparison. The resulting
martingale increment has the manuscript's bound η/16. -/
theorem abs_centeredTreeStep_sharp {N t : ℕ} {η : ℝ} (hη : 0 ≤ η)
    (u : Fin N → ℝ) (hu : ∀ i, u i ∈ Icc 0 1)
    (pick : RewardTape N t → Fin N) (i j : Fin N) (x : RewardTape N (t + 1)) :
    |centeredTreeStep η u pick i j x| ≤ η / 16 := by
  unfold centeredTreeStep
  split
  · let z := (supportedBase x.2.1 : ℝ)
    have hz₀ : 0 ≤ z := (supportedBase x.2.1).property.1
    have hz₁ : z ≤ 1 := (supportedBase x.2.1).property.2
    let b := η / 8 * z * (1 - z)
    have hb₀ : 0 ≤ b := by dsimp [b]; positivity
    have hb₁ : b ≤ η / 32 := by
      have h : z * (1 - z) ≤ 1 / 4 := by nlinarith only [sq_nonneg (z - 1 / 2)]
      have hl := mul_le_mul_of_nonneg_left h (div_nonneg hη (by norm_num : (0 : ℝ) ≤ 8))
      dsimp [b]
      linarith only [hl]
    have h₀ : (-1 : ℝ) ≤ u j - u i := by linarith only [(hu j).1, (hu i).2]
    have h₁ : u j - u i ≤ 1 := by linarith only [(hu j).2, (hu i).1]
    have hη' : 0 ≤ η / 48 := by positivity
    have he₀ := mul_le_mul_of_nonneg_left h₀ hη'
    have he₁ := mul_le_mul_of_nonneg_left h₁ hη'
    unfold boundedRoundReward bonusReward
    change |1 / 8 + z / 8 + b * (if _ then 1 else 0) -
      (1 / 8 + z / 8 + b * (if _ then 1 else 0)) - η / 48 * (u j - u i)| ≤ η / 16
    rw [abs_le]
    split_ifs <;> constructor <;> linarith only [hb₀, hb₁, he₀, he₁, hη]
  · rw [abs_zero]
    positivity

/-- From a deterministic policy on the observed past of the reward tape,
obtain the realized swap-regret lower bound with the exact martingale
error used in Theorem 4.1. The bonus probabilities are fixed in this step. -/
theorem expected_tape_swap_lower {N T : ℕ} (anchor : Fin N) {η : ℝ}
    (hη : 0 < η) (hη₁ : η ≤ 1) (u : ℕ → Fin N → ℝ)
    (hu : ∀ t < T, ∀ i, u t i ∈ Icc 0 1)
    (pick : (t : ℕ) → RewardTape N t → Fin N) (hp : ∀ t < T, Measurable (pick t)) :
    let I (ω : RewardTape N T) (t : ℕ) : Fin N :=
      if h : t < T then pick t (rewardTapePrefix N h.le ω) else anchor
    let q (ω : RewardTape N T) (t : ℕ) : Fin N → ℝ := Pi.single (I ω t) 1
    let y (ω : RewardTape N T) (t : ℕ) (i : Fin N) : ℝ :=
      if h : t < T then boundedRoundReward η (u t i) i (rewardTapePrefix N (Nat.succ_le_of_lt h) ω).2
      else 0
    η / 48 * (∫ ω, pseudoSwapRegret T (q ω) u ∂rewardTapeLaw N T) -
        N * (η / 16 * Real.sqrt (2 * T * Real.log (2 * N))) ≤
      ∫ ω, swapRegret T (y ω) (I ω) ∂rewardTapeLaw N T := by
  classical
  intro I q y
  have hy (t : ℕ) (ht : t < T) (ω : RewardTape N T) (j : Fin N) :
      y ω t j ∈ Icc 0 1 := by
    simpa only [y, dif_pos ht] using
      boundedRoundReward_mem hη.le hη₁ (u t j) j (rewardTapePrefix N (Nat.succ_le_of_lt ht) ω).2
  have hym (t : ℕ) (ht : t < T) (j : Fin N) : Measurable fun ω => y ω t j := by
    simp only [y, dif_pos ht]
    exact ((measurable_boundedRoundReward η (u t j) j).comp
        (measurable_snd : Measurable (Prod.snd : RewardTape N (t + 1) → ℝ × (Fin N → ℝ)))).comp
          (measurable_rewardTapePrefix N (Nat.succ_le_of_lt ht))
  have hIm (t : ℕ) (ht : t < T) : Measurable fun ω => I ω t := by
    simp only [I, dif_pos ht]
    exact (hp t ht).comp (measurable_rewardTapePrefix N ht.le)
  have hq (t : ℕ) (_ht : t < T) (ω : RewardTape N T) : IsProbVec (q ω t) := by
    dsimp [q]
    constructor
    · intro j
      rw [Pi.single_apply]
      split <;> norm_num
    · simp
  have hqm (t : ℕ) (ht : t < T) (j : Fin N) : Measurable fun ω => q ω t j := by
    exact (Measurable.of_discrete (f := fun a : Fin N => (Pi.single a (1 : ℝ) : Fin N → ℝ) j)).comp (hIm t ht)
  let d (i : Fin N) (t : ℕ) (j : Fin N) (ω : RewardTape N T) :=
    (Pi.single (I ω t) (1 : ℝ) : Fin N → ℝ) i * (y ω t j - y ω t i) -
      η / 48 * (q ω t i * (u t j - u t i))
  have he (t : ℕ) (ht : t < T) (i j : Fin N) :
      d i t j = centeredTreeStep η (u t) (pick t) i j ∘ rewardTapePrefix N (Nat.succ_le_of_lt ht) := by
    funext ω
    let pre := rewardTapePrefix N (Nat.succ_le_of_lt ht)
    have hpre : (pre ω).1 = rewardTapePrefix N ht.le ω := by
      have hf : rewardTapePrefix N (Nat.le_succ t) = (Prod.fst : RewardTape N (t + 1) → RewardTape N t) := by
        rw [rewardTapePrefix_succ N (le_refl t), rewardTapePrefix_refl, Function.id_comp]
      have h := congrFun (rewardTapePrefix_comp N (Nat.le_succ t) (Nat.succ_le_of_lt ht)) ω
      rw [hf] at h
      exact h
    simp only [d, q, centeredTreeStep, Function.comp_apply, I, y, dif_pos ht, Pi.single_apply]
    change (if i = pick t (rewardTapePrefix N ht.le ω) then (1 : ℝ) else 0) * _ -
      η / 48 * ((if i = pick t (rewardTapePrefix N ht.le ω) then (1 : ℝ) else 0) * _) =
        (if pick t (pre ω).1 = i then _ else 0)
    rw [hpre]
    by_cases h : pick t (rewardTapePrefix N ht.le ω) = i
    · simp [h]
    · have hn : i ≠ pick t (rewardTapePrefix N ht.le ω) := Ne.symm h
      simp [h, hn]
  refine expected_swapRegret_ge_proxy (rewardTapeLaw N T) (rewardTapeFiltration N T)
    anchor (η / 48) (η / 16) (by positivity) q (fun _ => u) y I hy hym hIm hq
    (fun t ht _ j => hu t ht j) hqm (fun _ _ _ => measurable_const) ?_ ?_ ?_
  · intro t ht i j
    change Measurable[rewardTapeFiltration N T (t + 1)] (d i t j)
    rw [he t ht i j]
    exact measurable_rewardTape_step ht _ (measurable_centeredTreeStep η (u t) (pick t) (hp t ht) i j)
  · intro t ht i j ω
    change |d i t j ω| ≤ η / 16
    rw [he t ht i j]
    exact abs_centeredTreeStep_sharp hη.le (u t) (hu t ht) (pick t) i j _
  · intro t ht i j
    change (rewardTapeLaw N T)[d i t j | rewardTapeFiltration N T t] =ᵐ[rewardTapeLaw N T] 0
    rw [he t ht i j]
    exact condExp_centeredTreeStep ht hη.le hη₁ (u t) (hu t ht) (pick t) (hp t ht) i j

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open MeasureTheory Set

/-- Append a period's independent draws to a tape for the preceding rounds. -/
def rewardTapeAppend (N start : ℕ) :
    (r : ℕ) → RewardTape N start × RewardTape N r → RewardTape N (start + r)
  | 0, p => p.1
  | r + 1, p => (rewardTapeAppend N start r (p.1, p.2.1), p.2.2)

theorem measurable_rewardTapeAppend (N start r : ℕ) :
    Measurable (rewardTapeAppend N start r) := by
  induction r with
  | zero => exact measurable_fst
  | succ r ih =>
    exact (ih.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
      (measurable_snd.comp measurable_snd)

theorem rewardTapeAppend_map (N start r : ℕ) :
    ((rewardTapeLaw N start).prod (rewardTapeLaw N r)).map (rewardTapeAppend N start r) =
      rewardTapeLaw N (start + r) := by
  induction r with
  | zero =>
    change ((rewardTapeLaw N start).prod (rewardTapeLaw N 0)).map Prod.fst = _
    rw [Measure.map_fst_prod, measure_univ, one_smul]
    rfl
  | succ r ih =>
    let A := RewardTape N start
    let B := RewardTape N r
    let D := ℝ × (Fin N → ℝ)
    let μ := rewardTapeLaw N start
    let ν := rewardTapeLaw N r
    let ρ := roundDrawLaw N
    let f := rewardTapeAppend N start r
    let assoc : (A × B) × D ≃ᵐ A × B × D := MeasurableEquiv.prodAssoc
    have hf : Measurable f := measurable_rewardTapeAppend N start r
    let g : A × (B × D) → RewardTape N (start + r) × D := rewardTapeAppend N start (r + 1)
    have hg : Measurable g := measurable_rewardTapeAppend N start (r + 1)
    have ha : MeasurePreserving assoc ((μ.prod ν).prod ρ) (μ.prod (ν.prod ρ)) :=
      measurePreserving_prodAssoc μ ν ρ
    have hmap : ((μ.prod ν).prod ρ).map (Prod.map f id) =
        (rewardTapeLaw N (start + r)).prod ρ := by
      rw [← Measure.map_prod_map _ _ hf measurable_id, Measure.map_id, ih]
    change (μ.prod (ν.prod ρ)).map g = (rewardTapeLaw N (start + r)).prod ρ
    rw [← ha.map_eq, Measure.map_map hg assoc.measurable]
    exact hmap

theorem rewardTapePrefix_append (N start : ℕ) {s r : ℕ} (hs : s ≤ r)
    (p : RewardTape N start) (q : RewardTape N r) :
    rewardTapePrefix N (Nat.add_le_add_left hs start) (rewardTapeAppend N start r (p, q)) =
      rewardTapeAppend N start s (p, rewardTapePrefix N hs q) := by
  induction hs with
  | refl =>
    simp only [rewardTapePrefix_refl, id_eq]
  | @step r hs ih =>
    have hf := rewardTapePrefix_succ N (Nat.add_le_add_left hs start)
    have hg := rewardTapePrefix_succ N hs
    change rewardTapePrefix N (Nat.le_succ_of_le (Nat.add_le_add_left hs start))
        (rewardTapeAppend N start (r + 1) (p, q)) =
      rewardTapeAppend N start s (p, rewardTapePrefix N (Nat.le_succ_of_le hs) q)
    rw [hf, hg]
    exact ih q.1

/-- Add the observations from a period to the history before it starts,
converting normalized observations back to the learner's raw reward scale. -/
noncomputable def historyAppend (start : ℕ) :
    (r : ℕ) → FeedbackHistory start × FeedbackHistory r → FeedbackHistory (start + r)
  | 0, p => p.1
  | r + 1, p => (historyAppend start r (p.1, p.2.1), 1 / 8 + p.2.2 / 8)

theorem measurable_historyAppend (start r : ℕ) : Measurable (historyAppend start r) := by
  induction r with
  | zero => exact measurable_fst
  | succ r ih =>
    exact (ih.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
      (measurable_const.add (((measurable_snd : Measurable (Prod.snd : FeedbackHistory r × ℝ → ℝ)).comp
        measurable_snd).div_const _))

/-- A bounded round reward on the normalized scale used in the information bound. -/
noncomputable def boundedObservation {N : ℕ} (η u : ℝ) (i : Fin N)
    (d : ℝ × (Fin N → ℝ)) : ℝ :=
  8 * boundedRoundReward η u i d - 1

theorem measurable_boundedObservation {N : ℕ} (η u : ℝ) (i : Fin N) :
    Measurable (boundedObservation η u i) :=
  ((measurable_boundedRoundReward η u i).const_mul _).sub measurable_const

theorem boundedObservation_ae {N : ℕ} (η u : ℝ) (i : Fin N) :
    boundedObservation η u i =ᵐ[roundDrawLaw N] observedReward η u i := by
  let Q : Measure ℝ := volume.restrict (Icc 0 1)
  let V : Measure ℝ := volume.restrict (Ico 0 1)
  have _ : IsProbabilityMeasure Q := ⟨by simp [Q, Real.volume_Icc]⟩
  have _ : IsProbabilityMeasure V := ⟨by simp [V, Real.volume_Ico]⟩
  let τ : Measure (Fin N → ℝ) := Measure.pi fun _ : Fin N => V
  have hbase : ∀ᵐ d ∂roundDrawLaw N, d.1 ∈ Icc (0 : ℝ) 1 := by
    apply ae_of_ae_map measurable_fst.aemeasurable
    change ∀ᵐ d ∂(Q.prod τ).map Prod.fst, d ∈ Icc (0 : ℝ) 1
    rw [Measure.map_fst_prod, measure_univ, one_smul]
    exact ae_restrict_mem measurableSet_Icc
  have hth : ∀ᵐ d ∂roundDrawLaw N, d.2 i ∈ Ico (0 : ℝ) 1 := by
    apply ae_of_ae_map ((measurable_pi_apply i).comp measurable_snd).aemeasurable
    change ∀ᵐ d ∂(Q.prod τ).map ((fun r => r i) ∘ Prod.snd), d ∈ Ico (0 : ℝ) 1
    rw [← Measure.map_map (measurable_pi_apply i) measurable_snd, Measure.map_snd_prod,
      measure_univ, one_smul, (measurePreserving_eval (fun _ : Fin N => V) i).map_eq]
    exact ae_restrict_mem measurableSet_Ico
  filter_upwards [hbase, hth] with d hz hd
  unfold boundedObservation boundedRoundReward bonusReward observedReward bonusTransform
  simp only [supportedBase, supportedThreshold, dif_pos hz, dif_pos hd, decide_eq_true_eq]
  split <;> ring

theorem measurable_rawTapeHistory {N : ℕ} (η : ℝ) (u : ℕ → Fin N → ℝ)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (hm : ∀ t, Measurable (pick t))
    (r : ℕ) : Measurable (rawTapeHistory η u pick r) := by
  induction r with
  | zero => exact measurable_const
  | succ r ih =>
    change Measurable (fun p : RewardTape N r × (ℝ × (Fin N → ℝ)) =>
      (rawTapeHistory η u pick r p.1,
        boundedRoundReward η (u r (pick r (rawTapeHistory η u pick r p.1)))
          (pick r (rawTapeHistory η u pick r p.1)) p.2))
    exact (ih.comp measurable_fst).prodMk
      (measurable_select ((hm r).comp (ih.comp measurable_fst)) fun i =>
        (measurable_boundedRoundReward η (u r i) i).comp measurable_snd)

/-- The same run with observations on the normalized scale. -/
noncomputable def boundedTapeTranscript {N : ℕ} (η : ℝ) (u : ℕ → Fin N → ℝ)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) :
    (t : ℕ) → RewardTape N t → FeedbackHistory t
  | 0, _ => ()
  | t + 1, p =>
    let past := boundedTapeTranscript η u pick t p.1
    let i := pick t past
    (past, boundedObservation η (u t i) i p.2)

theorem measurable_boundedTapeTranscript {N : ℕ} (η : ℝ) (u : ℕ → Fin N → ℝ)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (hm : ∀ t, Measurable (pick t))
    (r : ℕ) : Measurable (boundedTapeTranscript η u pick r) := by
  induction r with
  | zero => exact measurable_const
  | succ r ih =>
    change Measurable (fun p : RewardTape N r × (ℝ × (Fin N → ℝ)) =>
      (boundedTapeTranscript η u pick r p.1,
        boundedObservation η (u r (pick r (boundedTapeTranscript η u pick r p.1)))
          (pick r (boundedTapeTranscript η u pick r p.1)) p.2))
    exact (ih.comp measurable_fst).prodMk
      (measurable_select ((hm r).comp (ih.comp measurable_fst)) fun i =>
        (measurable_boundedObservation η (u r i) i).comp measurable_snd)

/-- Conditional on the past, the full learner in a period is precisely a
learner on the normalized observations made within that period. -/
theorem rawTapeHistory_append {N : ℕ} (η : ℝ) (u : ℕ → Fin N → ℝ)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (start r : ℕ)
    (past : RewardTape N start) (next : RewardTape N r) :
    let initial := rawTapeHistory η u pick start past
    let localPick (t : ℕ) (x : FeedbackHistory t) := pick (start + t) (historyAppend start t (initial, x))
    rawTapeHistory η u pick (start + r) (rewardTapeAppend N start r (past, next)) =
      historyAppend start r (initial,
        boundedTapeTranscript η (fun t => u (start + t)) localPick r next) := by
  intro initial localPick
  induction r with
  | zero => rfl
  | succ r ih =>
    let x := rawTapeHistory η u pick (start + r) (rewardTapeAppend N start r (past, next.1))
    let y := boundedTapeTranscript η (fun t => u (start + t)) localPick r next.1
    let hist := historyAppend start r (initial, y)
    let j (p : FeedbackHistory (start + r)) := pick (start + r) p
    change (x, boundedRoundReward η (u (start + r) (j x)) (j x) next.2) =
      (hist, 1 / 8 + boundedObservation η (u (start + r) (localPick r y)) (localPick r y) next.2 / 8)
    have hx : x = hist := ih next.1
    have hj : localPick r y = j hist := rfl
    rw [hx, hj]
    congr 1
    unfold boundedObservation
    ring

theorem rawTapeHistory_congr {N : ℕ} (η : ℝ) (u u' : ℕ → Fin N → ℝ)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (r : ℕ)
    (h : ∀ t < r, u t = u' t) (tape : RewardTape N r) :
    rawTapeHistory η u pick r tape = rawTapeHistory η u' pick r tape := by
  induction r with
  | zero => rfl
  | succ r ih =>
    have he := ih (fun t ht => h t (Nat.lt_succ_of_lt ht)) tape.1
    simp only [rawTapeHistory, he, h r (Nat.lt_succ_self r)]
    rfl

theorem boundedTapeTranscript_ae {N : ℕ} (η : ℝ) (u : ℕ → Fin N → ℝ)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (r : ℕ) :
    boundedTapeTranscript η u pick r =ᵐ[rewardTapeLaw N r] transcriptFromTape η u pick r := by
  induction r with
  | zero => exact Filter.EventuallyEq.rfl
  | succ r ih =>
    let μ := rewardTapeLaw N r
    let ν := roundDrawLaw N
    have hs : ∀ᵐ d ∂ν, ∀ i : Fin N,
        boundedObservation η (u r i) i d = observedReward η (u r i) i d :=
      ae_all_iff.mpr fun i => boundedObservation_ae η (u r i) i
    have hs' : ∀ᵐ p ∂μ.prod ν, ∀ i : Fin N,
        boundedObservation η (u r i) i p.2 = observedReward η (u r i) i p.2 :=
      (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae hs
    have hf' : ∀ᵐ p ∂μ.prod ν,
        boundedTapeTranscript η u pick r p.1 = transcriptFromTape η u pick r p.1 :=
      (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae ih
    change ∀ᵐ p ∂μ.prod ν,
      boundedTapeTranscript η u pick (r + 1) p = transcriptFromTape η u pick (r + 1) p
    filter_upwards [hf', hs'] with p hf hs
    change boundedTapeTranscript η u pick r p.1 = transcriptFromTape η u pick r p.1 at hf
    change ∀ i : Fin N, boundedObservation η (u r i) i p.2 = observedReward η (u r i) i p.2 at hs
    simp only [boundedTapeTranscript, transcriptFromTape, observationOfHistory]
    rw [hf, hs]

/-- The count of plays of one auxiliary action within a period of length r. -/
noncomputable def periodHits {N : ℕ} (η : ℝ) (u : ℕ → Fin N → ℝ)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (j : Fin N)
    (r : ℕ) (tape : RewardTape N r) : ℝ :=
  ∑ i : Fin r, if pick i (boundedTapeTranscript η u pick i (rewardTapePrefix N i.isLt.le tape)) = j
    then 1 else 0

private theorem measurable_playHit {A : Type*} [MeasurableSpace A] {N : ℕ} {a : A → Fin N}
    (ha : Measurable a) (j : Fin N) : Measurable fun x => if a x = j then (1 : ℝ) else 0 :=
  Measurable.ite (measurableSet_eq_fun ha measurable_const) measurable_const measurable_const

theorem integral_periodHits {h M U N : ℕ}
    (e : Fin N ≃ TreeAction h M U) (η : ℝ) (leaf : Fin (2 ^ h))
    (coin : TreeNode h → Bool) (leafCoin : ℕ → Bool) (dummy j : Fin M)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (hm : ∀ t, Measurable (pick t))
    (r : ℕ) :
    let u (t : ℕ) (i : Fin N) := treeBonusProb leaf coin (leafCoin t) j (e i)
    let A := treeAuxiliaryPeriod e η leaf coin leafCoin dummy pick hm
    let Q' := (volume.restrict (Icc (0 : ℝ) 1)).map (bonusTransform η)
    (∫ tape, periodHits η u pick (e.symm (.inr (.inl j))) r tape ∂rewardTapeLaw N r) =
      ∑ i : Fin r, ((A.experiment j).law Q' r).real ((A.experiment j).hit r i) := by
  classical
  intro u A Q'
  have hη : Measurable (bonusTransform η) := by unfold bonusTransform; fun_prop
  have _ : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := ⟨by simp [Real.volume_Icc]⟩
  have _ : IsProbabilityMeasure Q' := Measure.isProbabilityMeasure_map hη.aemeasurable
  let X := A.experiment j
  let target := e.symm (.inr (.inl j))
  let f (i : Fin r) (x : FeedbackHistory i) : ℝ := if pick i x = target then 1 else 0
  have hf (i : Fin r) : Measurable (f i) := measurable_playHit (hm i) target
  let pre (i : Fin r) := rewardTapePrefix N i.isLt.le
  let tr (i : Fin r) := boundedTapeTranscript η u pick i
  have htr (i : Fin r) : Measurable (tr i) := measurable_boundedTapeTranscript η u pick hm i
  have hpre (i : Fin r) : Measurable (pre i) := measurable_rewardTapePrefix N i.isLt.le
  let g (i : Fin r) (tape : RewardTape N r) := f i (tr i (pre i tape))
  have hg (i : Fin r) : Integrable (g i) (rewardTapeLaw N r) := by
    apply Integrable.of_bound ((hf i).comp ((htr i).comp (hpre i))).aestronglyMeasurable 1
    apply Filter.Eventually.of_forall
    intro x
    change ‖g i x‖ ≤ 1
    unfold g f
    split <;> simp
  change (∫ x, ∑ i, g i x ∂rewardTapeLaw N r) = ∑ i : Fin r, (X.law Q' r).real (X.hit r i)
  rw [integral_finsetSum _ (fun i _ => hg i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hmap :
      (rewardTapeLaw N i).map (tr i) = X.law Q' i :=
    (Measure.map_congr (boundedTapeTranscript_ae η u pick i)).trans
      (treeAuxiliaryPeriod_law_eq_map e η leaf coin leafCoin dummy j pick hm i)
  have htarget : f i = (X.query i).indicator (fun _ => (1 : ℝ)) := by
    funext x
    have he : x ∈ X.query i ↔ pick i x = target := Iff.rfl
    simp only [f, Set.indicator, he]
  calc
    _ = ∫ x, f i (tr i x) ∂rewardTapeLaw N i := by
      have he := integral_map (μ := rewardTapeLaw N r) (hpre i).aemeasurable ((hf i).comp (htr i)).aestronglyMeasurable
      rw [show (rewardTapeLaw N r).map (pre i) = rewardTapeLaw N i from rewardTapePrefix_map N i.isLt.le] at he
      exact he.symm
    _ = ∫ x, f i x ∂X.law Q' i := by
      have he := integral_map (μ := rewardTapeLaw N i) (htr i).aemeasurable (hf i).aestronglyMeasurable
      rw [hmap] at he
      exact he.symm
    _ = (X.law Q' i).real (X.query i) := by
      rw [htarget]
      exact integral_indicator_one (X.measurable_query i)
    _ = _ := congrArg ENNReal.toReal (X.law_hit Q' r i).symm

/-- The one-period bound in terms of the actual independent reward draws. -/
theorem integral_periodHits_average_le {h M U N : ℕ}
    (e : Fin N ≃ TreeAction h M U) (η : ℝ) (hη : 0 ≤ η) (hη₁ : η < 1)
    (leaf : Fin (2 ^ h)) (coin : TreeNode h → Bool) (leafCoin : ℕ → Bool) (dummy : Fin M)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (hm : ∀ t, Measurable (pick t)) (r : ℕ) :
    let u (j : Fin M) (t : ℕ) (i : Fin N) := treeBonusProb leaf coin (leafCoin t) j (e i)
    (∑ j : Fin M, ∫ tape, periodHits η (u j) pick (e.symm (.inr (.inl j))) r tape ∂rewardTapeLaw N r) / M
      ≤ (r : ℝ) / M + η * r * Real.sqrt ((r : ℝ) / (6 * M)) := by
  intro u
  have he (j : Fin M) :
      (∫ tape, periodHits η (u j) pick (e.symm (.inr (.inl j))) r tape ∂rewardTapeLaw N r) =
        ∑ i : Fin r, ((treeAuxiliaryPeriod e η leaf coin leafCoin dummy pick hm).experiment j |> fun X => (X.law ((volume.restrict (Icc (0 : ℝ) 1)).map (bonusTransform η)) r).real
            (X.hit r i)) :=
    integral_periodHits e η leaf coin leafCoin dummy j pick hm r
  rw [Finset.sum_congr rfl (fun j _ => he j)]
  exact tree_period_average_hits e η hη hη₁ leaf coin leafCoin dummy pick hm r

theorem boundedTapeTranscript_congr {N : ℕ} (η : ℝ) (u u' : ℕ → Fin N → ℝ)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (r : ℕ)
    (h : ∀ t < r, u t = u' t) (tape : RewardTape N r) :
    boundedTapeTranscript η u pick r tape = boundedTapeTranscript η u' pick r tape := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [boundedTapeTranscript, boundedTapeTranscript, ih (fun t ht => h t (Nat.lt_succ_of_lt ht)),
      h r (Nat.lt_succ_self r)]

/-- Count plays of one action in an interval on the full reward tape. -/
noncomputable def globalPeriodHits {N T : ℕ} (η : ℝ) (u : ℕ → Fin N → ℝ)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (a : Fin N)
    (start r : ℕ) (hend : start + r ≤ T) (tape : RewardTape N T) : ℝ :=
  ∑ i : Fin r, if pick (start + i)
    (rawTapeHistory η u pick (start + i)
      (rewardTapePrefix N ((Nat.add_le_add_left i.isLt.le start).trans hend) tape)) = a then 1 else 0

theorem measurable_globalPeriodHits {N T : ℕ} (η : ℝ) (u : ℕ → Fin N → ℝ)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (hm : ∀ t, Measurable (pick t))
    (a : Fin N) (start r : ℕ) (hend : start + r ≤ T) :
    Measurable (globalPeriodHits η u pick a start r hend) :=
  Finset.measurable_sum _ fun i _ => measurable_playHit
    ((hm (start + i)).comp ((measurable_rawTapeHistory η u pick hm (start + i)).comp
      (measurable_rewardTapePrefix N _))) a

theorem abs_globalPeriodHits {N T : ℕ} (η : ℝ) (u : ℕ → Fin N → ℝ)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (a : Fin N)
    (start r : ℕ) (hend : start + r ≤ T) (tape : RewardTape N T) :
    |globalPeriodHits η u pick a start r hend tape| ≤ r := by
  classical
  unfold globalPeriodHits
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ _ : Fin r, (1 : ℝ) := Finset.sum_le_sum fun _ _ => by split <;> norm_num
    _ = _ := by simp

private theorem integral_globalPeriodHits_prefix {N T : ℕ} (η : ℝ) (u : ℕ → Fin N → ℝ)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (hm : ∀ t, Measurable (pick t))
    (a : Fin N) (start r : ℕ) (hend : start + r ≤ T) :
    (∫ tape, globalPeriodHits η u pick a start r hend tape ∂rewardTapeLaw N T) =
      ∫ tape, globalPeriodHits η u pick a start r le_rfl tape ∂rewardTapeLaw N (start + r) := by
  have he := integral_map (μ := rewardTapeLaw N T) (measurable_rewardTapePrefix N hend).aemeasurable
    (measurable_globalPeriodHits η u pick hm a start r (le_refl (start + r))).aestronglyMeasurable
  rw [rewardTapePrefix_map] at he
  rw [he]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun tape => ?_
  unfold globalPeriodHits
  refine Finset.sum_congr rfl fun i _ => ?_
  have hcomp := congrFun (rewardTapePrefix_comp N (Nat.add_le_add_left i.isLt.le start) hend) tape
  dsimp only [Function.comp_apply] at hcomp
  rw [hcomp]

private theorem globalPeriodHits_append {N : ℕ} (η : ℝ) (u : ℕ → Fin N → ℝ)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (a : Fin N) (start r : ℕ)
    (past : RewardTape N start) (next : RewardTape N r) :
    let initial := rawTapeHistory η u pick start past
    let localPick (t : ℕ) (x : FeedbackHistory t) := pick (start + t) (historyAppend start t (initial, x))
    globalPeriodHits η u pick a start r le_rfl (rewardTapeAppend N start r (past, next)) =
      periodHits η (fun t => u (start + t)) localPick a r next := by
  intro initial localPick
  unfold globalPeriodHits periodHits
  refine Finset.sum_congr rfl fun i _ => ?_
  have hp := rewardTapePrefix_append N start i.isLt.le past next
  rw [hp]
  have hh := rawTapeHistory_append η u pick start i past (rewardTapePrefix N i.isLt.le next)
  rw [hh]

set_option maxHeartbeats 850000 in
/-- The one-period bound also holds after averaging over all earlier draws
in the global tape. Varying this period's selected action leaves the initial
history unchanged. -/
theorem tree_global_period_average {h M U N T : ℕ}
    (e : Fin N ≃ TreeAction h M U) (η : ℝ) (hη : 0 ≤ η) (hη₁ : η < 1)
    (active : ℕ → Fin (2 ^ h)) (leaf : Fin (2 ^ h)) (start r : ℕ) (hend : start + r ≤ T)
    (hbefore : ∀ t < start, active t ≠ leaf) (hwithin : ∀ t < r, active (start + t) = leaf)
    (coin : TreeNode h → Bool) (leafCoin : ℕ → Bool) (selected : Fin (2 ^ h) → Fin M)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (hm : ∀ t, Measurable (pick t)) :
    let aux (j : Fin M) := e.symm (.inr (.inl j))
    let u (j : Fin M) := scheduledBonuses e active coin leafCoin (Function.update selected leaf j)
    (∑ j : Fin M, ∫ tape, globalPeriodHits η (u j) pick (aux j) start r hend tape ∂rewardTapeLaw N T) / M
      ≤ (r : ℝ) / M + η * r * Real.sqrt ((r : ℝ) / (6 * M)) := by
  classical
  intro aux u
  let μ := rewardTapeLaw N start
  let ν := rewardTapeLaw N r
  let whole := scheduledBonuses e active coin leafCoin selected
  let payoff (j : Fin M) := globalPeriodHits η (u j) pick (aux j) start r (le_refl (start + r))
  let app := rewardTapeAppend N start r
  let F (j : Fin M) (p : RewardTape N start × RewardTape N r) := payoff j (app p)
  have hF (j : Fin M) : Integrable (F j) (μ.prod ν) := by
    apply Integrable.of_bound
      ((measurable_globalPeriodHits η (u j) pick hm (aux j) start r _).comp
        (measurable_rewardTapeAppend N start r)).aestronglyMeasurable r
    refine Filter.Eventually.of_forall fun p => ?_
    rw [Real.norm_eq_abs]
    exact abs_globalPeriodHits η (u j) pick (aux j) start r _ (app p)
  have hwhole (j : Fin M) :
      (∫ tape, globalPeriodHits η (u j) pick (aux j) start r hend tape ∂rewardTapeLaw N T) =
        ∫ p, (∫ next, F j (p, next) ∂ν) ∂μ := by
    rw [integral_globalPeriodHits_prefix η (u j) pick hm (aux j) start r hend]
    have he := integral_map (μ := μ.prod ν) (measurable_rewardTapeAppend N start r).aemeasurable
      (measurable_globalPeriodHits η (u j) pick hm (aux j) start r (le_refl (start + r))).aestronglyMeasurable
    change (∫ t, payoff j t ∂(μ.prod ν).map app) = ∫ p, F j p ∂μ.prod ν at he
    rw [show (μ.prod ν).map app = rewardTapeLaw N (start + r) from rewardTapeAppend_map N start r] at he
    exact he.trans (integral_prod (F j) (hF j))
  rw [Finset.sum_congr rfl (fun j _ => hwhole j), ← integral_finsetSum _ (fun j _ => (hF j).integral_prod_left),
    ← integral_div]
  let bound := (r : ℝ) / M + η * r * Real.sqrt ((r : ℝ) / (6 * M))
  have hf : Integrable (fun p => (∑ j : Fin M, ∫ next, F j (p, next) ∂ν) / M) μ :=
    (integrable_finsetSum _ fun j _ => (hF j).integral_prod_left).div_const _
  suffices h : ∀ p : RewardTape N start,
      (∑ j : Fin M, ∫ next, F j (p, next) ∂ν) / M ≤ bound by
    simpa only [integral_const, probReal_univ, one_smul] using integral_mono hf (integrable_const bound) h
  intro p
  let initial := rawTapeHistory η whole pick start p
  let localPick (t : ℕ) (x : FeedbackHistory t) := pick (start + t) (historyAppend start t (initial, x))
  have hlocal (t : ℕ) : Measurable (localPick t) :=
    (hm _).comp ((measurable_historyAppend start t).comp (measurable_const.prodMk measurable_id))
  let bonus (j : Fin M) (t : ℕ) (i : Fin N) := treeBonusProb leaf coin (leafCoin (start + t)) j (e i)
  have hprev (j : Fin M) : rawTapeHistory η (u j) pick start p = initial := by
    apply rawTapeHistory_congr
    intro t ht
    funext i
    simp only [u, whole, scheduledBonuses, Function.update_of_ne (hbefore t ht)]
  have hbonus (j : Fin M) (t : ℕ) (ht : t < r) : u j (start + t) = bonus j t := by
    funext i
    simp only [u, bonus, scheduledBonuses, hwithin t ht, Function.update_self]
  have heq (j : Fin M) (next : RewardTape N r) : F j (p, next) =
      periodHits η (bonus j) localPick (aux j) r next := by
    change globalPeriodHits η (u j) pick (aux j) start r le_rfl (rewardTapeAppend N start r (p, next)) = _
    rw [globalPeriodHits_append, hprev]
    change periodHits η (fun t => u j (start + t)) localPick (aux j) r next = _
    unfold periodHits
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [boundedTapeTranscript_congr _ _ (bonus j) _ _ (fun t ht => hbonus j t (ht.trans i.isLt))]
  rw [Finset.sum_congr rfl (fun j _ => integral_congr_ae (Filter.Eventually.of_forall (heq j)))]
  exact integral_periodHits_average_le e η hη hη₁ leaf coin (fun t => leafCoin (start + t))
    (selected leaf) localPick hlocal r

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

/-- The five weighted comparisons in Appendix D.1, Case 1.
The inputs are the nonnegative play masses in the six subtree events. -/
theorem internal_left_gain {H gain total x₁ x₂ x₃ x₄ x₅ x₆ : ℝ}
    (hH : 1 ≤ H) (hg : 0 ≤ gain)
    (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂) (hx₃ : 0 ≤ x₃)
    (hx₄ : 0 ≤ x₄) (hx₅ : 0 ≤ x₅)
    (h₁ : 16 * H ^ 4 * x₁ + 32 * H ^ 4 * x₂ ≤ 128 * H ^ 5 * gain)
    (h₂ : 8 * H ^ 3 * x₃ - 8 * H ^ 4 * x₂ - 8 * H ^ 4 * x₁ ≤ 32 * H ^ 4 * gain)
    (h₃ : 8 * H ^ 2 * x₅ + 4 * H ^ 2 * x₄ - 4 * H ^ 3 * (x₁ + x₂ + x₃) ≤
      16 * H ^ 3 * gain)
    (h₄ : 2 * H * x₆ - 2 * H ^ 2 * x₅ - 2 * H ^ 2 * x₄ -
      2 * H ^ 2 * (x₁ + x₂ + x₃) ≤ 4 * H ^ 2 * gain)
    (h₅ : total - 2 * H * (x₁ + x₂ + x₃ + x₄ + x₅ + x₆) ≤ 4 * H * gain) :
    total / (184 * H ^ 5) ≤ gain := by
  have hpos : 0 < H := by linarith
  have hgap : 0 ≤ H - 1 := sub_nonneg.mpr hH
  let c₁ := 2 * H * (H - 1) * (4 * H ^ 2 + 2 * H + 1)
  let c₂ := 16 * H ^ 4 + c₁
  let c₃ := 2 * H * (H - 1) * (2 * H + 1)
  let c₄ := 2 * H * (H - 1)
  let c₅ := 2 * H * (3 * H - 1)
  have hc₁ : 0 ≤ c₁ := by dsimp [c₁]; positivity
  have hc₂ : 0 ≤ c₂ := by dsimp [c₂]; positivity
  have hc₃ : 0 ≤ c₃ := by dsimp [c₃]; positivity
  have hc₄ : 0 ≤ c₄ := by dsimp [c₄]; positivity
  have hc₅ : 0 ≤ c₅ := by
    have h : 0 ≤ 3 * H - 1 := by linarith
    dsimp [c₅]
    positivity
  have hsum : total + c₁ * x₁ + c₂ * x₂ + c₃ * x₃ + c₄ * x₄ + c₅ * x₅ ≤
      (128 * H ^ 5 + 32 * H ^ 4 + 16 * H ^ 3 + 4 * H ^ 2 + 4 * H) * gain := by
    dsimp [c₁, c₂, c₃, c₄, c₅]
    linear_combination h₁ + h₂ + h₃ + h₄ + h₅
  have hmass : total ≤ total + c₁ * x₁ + c₂ * x₂ + c₃ * x₃ + c₄ * x₄ + c₅ * x₅ := by
    linarith only [mul_nonneg hc₁ hx₁, mul_nonneg hc₂ hx₂, mul_nonneg hc₃ hx₃,
      mul_nonneg hc₄ hx₄, mul_nonneg hc₅ hx₅]
  have hcoeff : 128 * H ^ 5 + 32 * H ^ 4 + 16 * H ^ 3 + 4 * H ^ 2 + 4 * H ≤
      184 * H ^ 5 := by
    have p (n : ℕ) (hn : n ≤ 5) : H ^ n ≤ H ^ 5 := pow_le_pow_right₀ hH hn
    nlinarith only [p 4 (by omega), p 3 (by omega), p 2 (by omega), p 1 (by omega),
      show H ^ 1 = H by ring]
  apply (div_le_iff₀ (by positivity)).mpr
  calc
    total ≤ _ := hmass.trans hsum
    _ ≤ 184 * H ^ 5 * gain := mul_le_mul_of_nonneg_right hcoeff hg
    _ = gain * (184 * H ^ 5) := mul_comm _ _

/-- Cases 2 and 3 use the same inequalities for the relevant groups of
rounds. In Case 3 the second group has zero mass. -/
theorem internal_three_comparisons {H gain total x₁ x₂ x₃ : ℝ}
    (hH : 1 ≤ H) (hg : 0 ≤ gain) (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂)
    (h₁ : 4 * H ^ 2 * x₁ + 8 * H ^ 2 * x₂ ≤ 16 * H ^ 3 * gain)
    (h₂ : 2 * H * x₃ - 2 * H ^ 2 * (x₁ + x₂) ≤ 4 * H ^ 2 * gain)
    (h₃ : total - 2 * H * (x₁ + x₂ + x₃) ≤ 4 * H * gain) :
    total / (184 * H ^ 5) ≤ gain := by
  have hpos : 0 < H := by linarith
  have hgap : 0 ≤ H - 1 := sub_nonneg.mpr hH
  have hgap' : 0 ≤ 3 * H - 1 := by linarith
  have hsum : total + 2 * H * (H - 1) * x₁ + 2 * H * (3 * H - 1) * x₂ ≤
      (16 * H ^ 3 + 4 * H ^ 2 + 4 * H) * gain := by
    linear_combination h₁ + h₂ + h₃
  have hmass : total ≤ total + 2 * H * (H - 1) * x₁ + 2 * H * (3 * H - 1) * x₂ := by
    have h₁ : 0 ≤ 2 * H * (H - 1) * x₁ := by positivity
    have h₂ : 0 ≤ 2 * H * (3 * H - 1) * x₂ := by positivity
    linarith
  have hcoeff : 16 * H ^ 3 + 4 * H ^ 2 + 4 * H ≤ 184 * H ^ 5 := by
    have p (n : ℕ) (hn : n ≤ 5) : H ^ n ≤ H ^ 5 := pow_le_pow_right₀ hH hn
    nlinarith only [p 3 (by omega), p 2 (by omega), p 1 (by omega),
      show H ^ 1 = H by ring, show 0 ≤ H ^ 5 by positivity]
  exact (div_le_iff₀ (by positivity)).mpr (by
    rw [mul_comm gain]
    exact (hmass.trans hsum).trans (mul_le_mul_of_nonneg_right hcoeff hg))

/-- Case 4 only compares against the right child and the root. -/
theorem internal_two_comparisons {H gain total right : ℝ}
    (hH : 1 ≤ H) (hg : 0 ≤ gain)
    (h₁ : 2 * H * right ≤ 4 * H ^ 2 * gain)
    (h₂ : total - 2 * H * right ≤ 4 * H * gain) :
    total / (184 * H ^ 5) ≤ gain := by
  have hpos : 0 < H := by linarith
  have hsum : total ≤ (4 * H ^ 2 + 4 * H) * gain := by linear_combination h₁ + h₂
  have hcoeff : 4 * H ^ 2 + 4 * H ≤ 184 * H ^ 5 := by
    have p (n : ℕ) (hn : n ≤ 5) : H ^ n ≤ H ^ 5 := pow_le_pow_right₀ hH hn
    nlinarith only [p 2 (by omega), p 1 (by omega),
      show H ^ 1 = H by ring, show 0 ≤ H ^ 5 by positivity]
  exact (div_le_iff₀ (by positivity)).mpr (by
    rw [mul_comm gain]
    exact hsum.trans (mul_le_mul_of_nonneg_right hcoeff hg))

/-- The five averaged comparisons for a left action with internal children,
before rescaling to a common denominator. -/
theorem internal_left_gain_of_comparisons {H gain total x₁ x₂ x₃ x₄ x₅ x₆ : ℝ}
    (hH : 1 ≤ H) (hg : 0 ≤ gain)
    (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂) (hx₃ : 0 ≤ x₃)
    (hx₄ : 0 ≤ x₄) (hx₅ : 0 ≤ x₅)
    (h₁ : x₁ / (8 * H) + x₂ / (4 * H) ≤ gain)
    (h₂ : x₃ / (4 * H) - (x₁ + x₂) / 4 ≤ gain)
    (h₃ : x₅ / (2 * H) + x₄ / (4 * H) - (x₁ + x₂ + x₃) / 4 ≤ gain)
    (h₄ : x₆ / (2 * H) - (x₅ + x₄ + x₁ + x₂ + x₃) / 2 ≤ gain)
    (h₅ : total / (4 * H) - (x₁ + x₂ + x₃ + x₄ + x₅ + x₆) / 2 ≤ gain) :
    total / (184 * H ^ 5) ≤ gain := by
  have h : 0 < H := by linarith
  refine internal_left_gain (x₆ := x₆) hH hg hx₁ hx₂ hx₃ hx₄ hx₅ ?_ ?_ ?_ ?_ ?_
  · have he : (128 * H ^ 5) * (x₁ / (8 * H) + x₂ / (4 * H)) =
        16 * H ^ 4 * x₁ + 32 * H ^ 4 * x₂ := by
      field_simp [ne_of_gt h]
      ring
    simpa only [he] using mul_le_mul_of_nonneg_left h₁ (show 0 ≤ 128 * H ^ 5 by positivity)
  · have he : (32 * H ^ 4) * (x₃ / (4 * H) - (x₁ + x₂) / 4) =
        8 * H ^ 3 * x₃ - 8 * H ^ 4 * x₂ - 8 * H ^ 4 * x₁ := by
      field_simp [ne_of_gt h]
      ring
    simpa only [he] using mul_le_mul_of_nonneg_left h₂ (show 0 ≤ 32 * H ^ 4 by positivity)
  · have he : (16 * H ^ 3) * (x₅ / (2 * H) + x₄ / (4 * H) - (x₁ + x₂ + x₃) / 4) =
        8 * H ^ 2 * x₅ + 4 * H ^ 2 * x₄ - 4 * H ^ 3 * (x₁ + x₂ + x₃) := by
      field_simp [ne_of_gt h]
      ring
    simpa only [he] using mul_le_mul_of_nonneg_left h₃ (show 0 ≤ 16 * H ^ 3 by positivity)
  · have he : (4 * H ^ 2) * (x₆ / (2 * H) - (x₅ + x₄ + x₁ + x₂ + x₃) / 2) =
        2 * H * x₆ - 2 * H ^ 2 * x₅ - 2 * H ^ 2 * x₄ - 2 * H ^ 2 * (x₁ + x₂ + x₃) := by
      field_simp [ne_of_gt h]
      ring
    simpa only [he] using mul_le_mul_of_nonneg_left h₄ (show 0 ≤ 4 * H ^ 2 by positivity)
  · have he : (4 * H) * (total / (4 * H) - (x₁ + x₂ + x₃ + x₄ + x₅ + x₆) / 2) =
        total - 2 * H * (x₁ + x₂ + x₃ + x₄ + x₅ + x₆) := by
      field_simp [ne_of_gt h]
      ring
    simpa only [he] using mul_le_mul_of_nonneg_left h₅ (show 0 ≤ 4 * H by positivity)

/-- The three averaged comparisons for a right action with internal children. -/
theorem internal_right_gain_of_comparisons {H gain total x₁ x₂ x₃ : ℝ}
    (hH : 1 ≤ H) (hg : 0 ≤ gain) (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂)
    (h₁ : x₂ / (2 * H) + x₁ / (4 * H) ≤ gain)
    (h₂ : x₃ / (2 * H) - (x₁ + x₂) / 2 ≤ gain)
    (h₃ : total / (4 * H) - (x₁ + x₂ + x₃) / 2 ≤ gain) :
    total / (184 * H ^ 5) ≤ gain := by
  have h : 0 < H := by linarith
  refine internal_three_comparisons (x₃ := x₃) hH hg hx₁ hx₂ ?_ ?_ ?_
  · have he : (16 * H ^ 3) * (x₂ / (2 * H) + x₁ / (4 * H)) =
        4 * H ^ 2 * x₁ + 8 * H ^ 2 * x₂ := by
      field_simp [ne_of_gt h]
      ring
    simpa only [he] using mul_le_mul_of_nonneg_left h₁ (show 0 ≤ 16 * H ^ 3 by positivity)
  · have he : (4 * H ^ 2) * (x₃ / (2 * H) - (x₁ + x₂) / 2) =
        2 * H * x₃ - 2 * H ^ 2 * (x₁ + x₂) := by
      field_simp [ne_of_gt h]
      ring
    simpa only [he] using mul_le_mul_of_nonneg_left h₂ (show 0 ≤ 4 * H ^ 2 by positivity)
  · have he : (4 * H) * (total / (4 * H) - (x₁ + x₂ + x₃) / 2) =
        total - 2 * H * (x₁ + x₂ + x₃) := by
      field_simp [ne_of_gt h]
      ring
    simpa only [he] using mul_le_mul_of_nonneg_left h₃ (show 0 ≤ 4 * H by positivity)

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open Set

/-- Number of plays of one action while leaves in the indicated subtree
are active, with a fixed private seed and reward tape. -/
noncomputable def subtreePlayMass {h M U : ℕ}
    (pick : (t : ℕ) → FeedbackHistory t → TreeAction h M U)
    (active : ℕ → Fin (2 ^ h)) (w : TreeNode h)
    (η : ℝ) (coin : TreeNode h → Bool) (leafCoin : ℕ → Bool)
    (selected : Fin (2 ^ h) → Fin M) (z : ℕ → Icc (0 : ℝ) 1)
    (draw : ℕ → TreeAction h M U → Ico (0 : ℝ) 1) (T : ℕ)
    (a : TreeAction h M U) : ℝ :=
  let y (t : ℕ) := treeReward η (active t) coin (leafCoin t) (selected (active t)) (z t) (draw t)
  ∑ t ∈ Finset.range T, if w.active (active t) ∧ pick t (feedbackHistory pick y t) = a then 1 else 0

/-- Play mass accrued in an earlier subtree is invariant under changing
a coin that first influences rewards after that subtree has been visited. -/
theorem subtreePlayMass_update_of_before {h M U : ℕ}
    (pick : (t : ℕ) → FeedbackHistory t → TreeAction h M U)
    (active : ℕ → Fin (2 ^ h)) (ha : Monotone active) (w v : TreeNode h)
    (hbefore : w.last ≤ v.mid)
    (η : ℝ) (coin : TreeNode h → Bool) (leafCoin : ℕ → Bool)
    (selected : Fin (2 ^ h) → Fin M) (z : ℕ → Icc (0 : ℝ) 1)
    (draw : ℕ → TreeAction h M U → Ico (0 : ℝ) 1) (T : ℕ)
    (a : TreeAction h M U) (b : Bool) :
    subtreePlayMass pick active w η (Function.update coin v b) leafCoin selected z draw T a =
      subtreePlayMass pick active w η coin leafCoin selected z draw T a := by
  classical
  unfold subtreePlayMass
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases ht : w.active (active t)
  · have ht' : (active t : ℕ) < v.mid := lt_of_lt_of_le ht.2 hbefore
    have hprior (s : ℕ) (hs : s < t) : (active s : ℕ) < v.mid := lt_of_le_of_lt (ha hs.le) ht'
    have he := action_eq_of_update_before_right pick active v b η coin leafCoin selected z draw t hprior
    dsimp at he
    rw [he]
  · simp [ht]

private theorem pair_gain_lower {N T : ℕ} (q u : ℕ → Fin N → ℝ) (i a b : Fin N)
    (w : ℕ → ℝ) (hq : ∀ t < T, 0 ≤ q t i)
    (hw : ∀ t < T, w t ≤ (u t a + u t b) / 2 - u t i) :
    (∑ t ∈ Finset.range T, q t i * w t) ≤ bestSwapGain T q u i := by
  have hs := Finset.sum_le_sum (s := Finset.range T) fun t ht =>
    mul_le_mul_of_nonneg_left (hw t (Finset.mem_range.mp ht)) (hq t (Finset.mem_range.mp ht))
  have he : (∑ t ∈ Finset.range T, q t i * ((u t a + u t b) / 2 - u t i)) =
      (swapGain T q u i a + swapGain T q u i b) / 2 := by
    rw [swapGain, swapGain, ← Finset.sum_add_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun t _ => by ring
  rw [he] at hs
  linarith only [hs, swapGain_le_best (T := T) q u i a, swapGain_le_best (T := T) q u i b]

/-- The two child comparisons for the left action at depth one above the
leaves. The left comparison uses the event that the parent switches on the right. -/
theorem deepest_left_comparisons {h M U N T : ℕ} (e : Fin N ≃ TreeAction h M U)
    (v : TreeNode h) (hv : (v.1 : ℕ) + 1 = h)
    (active : ℕ → Fin (2 ^ h)) (coin : TreeNode h → Bool) (leafCoin : ℕ → Bool)
    (selected : Fin (2 ^ h) → Fin M) (q : ℕ → Fin N → ℝ)
    (hq : ∀ t < T, ∀ i, 0 ≤ q t i) :
    let i := e.symm (.inl (v, false))
    let l := v.child (by omega) false
    let r := v.child (by omega) true
    let u (t : ℕ) (j : Fin N) := treeBonusProb (active t) coin (leafCoin t) (selected (active t)) (e j)
    let c := 1 / (2 * treeHeight h)
    (coin v = true →
      (∑ t ∈ Finset.range T, q t i * (if l.active (active t) then c else 0)) ≤ bestSwapGain T q u i) ∧
    (∑ t ∈ Finset.range T, q t i *
      (if r.active (active t) then c else if l.active (active t) then -(1 / 2) else 0))
      ≤ bestSwapGain T q u i := by
  intro i l r u c
  have hd : (v.1 : ℕ) < h := by omega
  have hd' : (((v.1 : ℕ) : ℝ) + 1) = h := by exact_mod_cast hv
  have halg : 1 / 2 - (((v.1 : ℕ) : ℝ) + 1) / (2 * treeHeight h) = c := by
    rw [hd']
    dsimp [c, treeHeight]
    field_simp
    ring
  have haux (t : ℕ) :
      u t i = if v.active (active t) then
        if (active t : ℕ) < v.mid ∨ coin v = false then 1 / 2 - c else 0 else 0 := by
    have hval : (((v.1 : ℕ) : ℝ) + 1) / (2 * treeHeight h) = 1 / 2 - c := by
      linarith only [halg]
    by_cases ha : v.active (active t)
    · by_cases hb : (active t : ℕ) < v.mid
      · simp [u, i, treeBonusProb, hd.ne, ha, hb, hval]
      · cases he : coin v <;> simp [u, i, treeBonusProb, hd.ne, ha, hb, he, hval]
    · simp [u, i, treeBonusProb, ha]
  have hpair (w : TreeNode h) (hw : (w.1 : ℕ) = h) (t : ℕ) :
      u t (e.symm (.inl (w, false))) + u t (e.symm (.inl (w, true))) =
        if w.active (active t) then 1 else 0 := by
    by_cases ha : w.active (active t)
    · simpa [u, ha] using treeBonusProb_leaf_pair (U := U) (active t) w hw ha coin
        (leafCoin t) (selected (active t))
    · simp [u, treeBonusProb, ha]
  have hH : 0 < treeHeight h := by unfold treeHeight; positivity
  have hnonneg : 0 ≤ c := by dsimp [c]; positivity
  have hcle : c ≤ 1 / 2 := by
    have h : 0 ≤ (((v.1 : ℕ) : ℝ) + 1) / (2 * treeHeight h) := by positivity
    linarith only [halg, h]
  have hchild (t : ℕ) :=
    v.child_active_iff hd (active t)
  change (∀ t, ((l.active (active t) ↔ v.active (active t) ∧ (active t : ℕ) < v.mid) ∧
      (r.active (active t) ↔ v.active (active t) ∧ v.mid ≤ (active t : ℕ)))) at hchild
  constructor
  · intro hcoin
    apply pair_gain_lower q u i (e.symm (.inl (l, false))) (e.symm (.inl (l, true))) _
      (fun t ht => hq t ht i)
    intro t _
    rw [hpair l hv, haux t]
    by_cases ha : v.active (active t)
    · by_cases hb : (active t : ℕ) < v.mid
      · simp [(hchild t).1, ha, hb]
      · simp [(hchild t).1, ha, hb, hcoin]
    · simp [(hchild t).1, ha]
  · apply pair_gain_lower q u i (e.symm (.inl (r, false))) (e.symm (.inl (r, true))) _
      (fun t ht => hq t ht i)
    intro t _
    rw [hpair r hv, haux t]
    by_cases ha : v.active (active t)
    · by_cases hb : (active t : ℕ) < v.mid
      · have hc : ¬v.mid ≤ (active t : ℕ) := not_le_of_gt hb
        simp only [(hchild t).1, (hchild t).2, ha, hb, hc, true_and, true_or, if_true, if_false]
        linarith only [hnonneg]
      · have hc := le_of_not_gt hb
        simp only [(hchild t).2, ha, true_and, hc, if_true, hb, false_or]
        split <;> linarith only [hcle]
    · simp [(hchild t).1, (hchild t).2, ha]

private theorem weighted_gain_bound {N T : ℕ} (q u : ℕ → Fin N → ℝ) (i j : Fin N)
    (w : ℕ → ℝ) (hq : ∀ t < T, 0 ≤ q t i) (hw : ∀ t < T, w t ≤ u t j - u t i) :
    (∑ t ∈ Finset.range T, q t i * w t) ≤ bestSwapGain T q u i := by
  exact (Finset.sum_le_sum (s := Finset.range T) fun t ht => mul_le_mul_of_nonneg_left
    (hw t (Finset.mem_range.mp ht)) (hq t (Finset.mem_range.mp ht))).trans
      (swapGain_le_best q u i j)

/-- Swapping an internal action to the right child's left action gains
one level of bonus on the right subtree when the child does not switch. -/
theorem internal_right_child_first {h M U N T : ℕ} (e : Fin N ≃ TreeAction h M U)
    (v : TreeNode h) (hv : (v.1 : ℕ) + 1 < h) (side : Bool)
    (active : ℕ → Fin (2 ^ h)) (coin : TreeNode h → Bool) (leafCoin : ℕ → Bool)
    (selected : Fin (2 ^ h) → Fin M) (q : ℕ → Fin N → ℝ)
    (hq : ∀ t < T, ∀ i, 0 ≤ q t i) :
    let i := e.symm (.inl (v, side))
    let w := v.child (by omega) true
    let u (t : ℕ) (j : Fin N) := treeBonusProb (active t) coin (leafCoin t) (selected (active t)) (e j)
    let c := 1 / (2 * treeHeight h)
    coin w = false →
    (∑ t ∈ Finset.range T, q t i *
      (if w.active (active t) then c
       else if v.active (active t) ∧ side = false then -(1 / 2) else 0)) ≤ bestSwapGain T q u i := by
  intro i w u c hc
  have hd : (v.1 : ℕ) < h := by omega
  have hw : (w.1 : ℕ) < h := hv
  have hH : 0 < treeHeight h := by unfold treeHeight; positivity
  let d : ℝ := ((v.1 : ℕ) : ℝ) + 1
  let d' : ℝ := ((w.1 : ℕ) : ℝ) + 1
  have he : d' = d + 1 := by simp [d', d, w, TreeNode.child]
  have hfrac : d / (2 * treeHeight h) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    dsimp [d, treeHeight]
    have hdepth : ((v.1 : ℕ) : ℝ) ≤ h := by exact_mod_cast hd.le
    linarith
  have hdiff : d' / (2 * treeHeight h) - d / (2 * treeHeight h) = c := by
    rw [← sub_div, he, add_sub_cancel_left]
  apply weighted_gain_bound q u i (e.symm (.inl (w, false))) _ (fun t ht => hq t ht i)
  intro t _
  by_cases hr : w.active (active t)
  · have ha := ((v.child_active_iff hd (active t)).2).mp hr
    have hsource : u t i ≤ d / (2 * treeHeight h) := by
      simp only [u, i, Equiv.apply_symm_apply, treeBonusProb, ha.1, hd.ne, not_lt_of_ge ha.2,
        if_true, if_false]
      split
      · exact le_rfl
      · exact div_nonneg (by unfold d; positivity) (by positivity)
    have htarget : u t (e.symm (.inl (w, false))) = d' / (2 * treeHeight h) := by
      by_cases hwr : (active t : ℕ) < w.mid <;>
        simp [u, treeBonusProb, hr, hw.ne, hwr, hc, d']
    rw [if_pos hr, ← hdiff, htarget]
    exact sub_le_sub_left hsource _
  · rw [if_neg hr]
    have htarget : u t (e.symm (.inl (w, false))) = 0 := by simp [u, treeBonusProb, hr]
    rw [htarget, zero_sub]
    by_cases ha : v.active (active t)
    · have hleft : (active t : ℕ) < v.mid := lt_of_not_ge fun h => hr ((v.child_active_iff hd (active t)).2.mpr ⟨ha, h⟩)
      cases side
      · simpa [u, i, treeBonusProb, ha, hd.ne, hleft, d] using neg_le_neg hfrac
      · simp [u, i, treeBonusProb, ha, hd.ne, hleft]
    · simp [u, i, treeBonusProb, ha]

/-- Root comparison for either action of an internal node. The left action
can get a bonus anywhere in the node's subtree. The right action can get a
bonus only in the right child's subtree. -/
theorem internal_root_support_gain {h M U N T : ℕ} (e : Fin N ≃ TreeAction h M U)
    (v : TreeNode h) (hv : (v.1 : ℕ) < h) (side : Bool)
    (active : ℕ → Fin (2 ^ h)) (coin : TreeNode h → Bool) (leafCoin : ℕ → Bool)
    (selected : Fin (2 ^ h) → Fin M) (q : ℕ → Fin N → ℝ)
    (hq : ∀ t < T, ∀ i, 0 ≤ q t i) :
    let i := e.symm (.inl (v, side))
    let w := if side then v.child hv true else v
    let u (t : ℕ) (j : Fin N) := treeBonusProb (active t) coin (leafCoin t) (selected (active t)) (e j)
    (∑ t ∈ Finset.range T, q t i) / (4 * treeHeight h) -
      (∑ t ∈ Finset.range T, if w.active (active t) then q t i else 0) / 2 ≤ bestSwapGain T q u i := by
  intro i w u
  let a := e.symm (.inl (TreeNode.root h, false))
  let b := e.symm (.inl (TreeNode.root h, true))
  have hh : 0 < h := by omega
  have hH : 0 < treeHeight h := by unfold treeHeight; positivity
  have hdepth : ((v.1 : ℕ) : ℝ) ≤ h := by exact_mod_cast hv.le
  have hfrac : (((v.1 : ℕ) : ℝ) + 1) / (2 * treeHeight h) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    unfold treeHeight
    linarith
  have hr (t : ℕ) (_ht : t < T) : u t a + u t b = 1 / (2 * treeHeight h) := by
    simpa only [u, a, b, Equiv.apply_symm_apply] using
      treeBonusProb_root_pair (U := U) hh (active t) coin (leafCoin t) (selected (active t))
  have hi (t : ℕ) : u t i ≤ if w.active (active t) then 1 / 2 else 0 := by
    by_cases ht : v.active (active t)
    · by_cases he : (active t : ℕ) < v.mid
      · have hx : ¬ (v.child hv true).active (active t) := by
          intro ha
          exact (not_le_of_gt he) ((v.child_active_iff hv (active t)).2.mp ha).2
        cases side
        · simp [w, u, i, treeBonusProb, ht, hv.ne, he]
          simpa only [one_div] using hfrac
        · simp [w, u, i, treeBonusProb, ht, hv.ne, he, hx]
      · have hx : (v.child hv true).active (active t) :=
          (v.child_active_iff hv (active t)).2.mpr ⟨ht, le_of_not_gt he⟩
        cases side <;> cases hcoin : coin v <;>
          simp [w, u, i, treeBonusProb, ht, hv.ne, he, hx, hcoin] <;> simpa only [one_div] using hfrac
    · have hx : ¬ (v.child hv true).active (active t) :=
        fun ha => ht ((v.child_active_iff hv (active t)).2.mp ha).1
      cases side <;> simp [w, u, i, treeBonusProb, ht, hx]
  have hs (t : ℕ) (ht : t < T) :
      q t i * u t i ≤ (if w.active (active t) then q t i else 0) / 2 := by
    by_cases h : w.active (active t)
    · rw [if_pos h]
      have hb := hi t
      rw [if_pos h] at hb
      have he : q t i * (1 / 2) = q t i / 2 := by ring
      exact (mul_le_mul_of_nonneg_left hb (hq t ht i)).trans_eq he
    · rw [if_neg h, zero_div]
      have hh : u t i ≤ 0 := by simpa only [if_neg h] using hi t
      exact mul_nonpos_of_nonneg_of_nonpos (hq t ht i) hh
  have hsum := Finset.sum_le_sum (s := Finset.range T) fun t ht => hs t (Finset.mem_range.mp ht)
  rw [← Finset.sum_div] at hsum
  linarith only [hsum, root_bestSwapGain q u i a b (treeHeight h) hr]

/-- Case 4 of Appendix D.1, with both the right-child and root comparisons. -/
theorem deepest_right_bestSwapGain {h M U N T : ℕ} (e : Fin N ≃ TreeAction h M U)
    (v : TreeNode h) (hv : (v.1 : ℕ) + 1 = h)
    (active : ℕ → Fin (2 ^ h)) (coin : TreeNode h → Bool) (leafCoin : ℕ → Bool)
    (selected : Fin (2 ^ h) → Fin M) (q : ℕ → Fin N → ℝ)
    (hq : ∀ t < T, ∀ i, 0 ≤ q t i) :
    let i := e.symm (.inl (v, true))
    let u (t : ℕ) (j : Fin N) := treeBonusProb (active t) coin (leafCoin t) (selected (active t)) (e j)
    (∑ t ∈ Finset.range T, q t i) / (184 * treeHeight h ^ 5) ≤ bestSwapGain T q u i := by
  intro i u
  let H := treeHeight h
  let Q := ∑ t ∈ Finset.range T, q t i
  let R := ∑ t ∈ Finset.range T, if (v.child (by omega) true).active (active t) then q t i else 0
  let G := bestSwapGain T q u i
  have hH : 1 ≤ H := by dsimp [H, treeHeight]; linarith [Nat.cast_nonneg (α := ℝ) h]
  have hH' : 0 < H := zero_lt_one.trans_le hH
  have hchild : R / (2 * H) ≤ G := deepest_right_gain e v hv active coin leafCoin selected q hq
  have hroot : Q / (4 * H) - R / 2 ≤ G := by
    simpa only [Bool.true_eq, if_true] using
      internal_root_support_gain e v (by omega) true active coin leafCoin selected q hq
  have h1 : 2 * H * R ≤ 4 * H ^ 2 * G := by
    have hm := (div_le_iff₀ (show 0 < 2 * H by positivity)).mp hchild
    nlinarith only [mul_le_mul_of_nonneg_left hm (show 0 ≤ 2 * H by positivity)]
  have h2 : Q - 2 * H * R ≤ 4 * H * G := by
    have h := mul_le_mul_of_nonneg_right hroot (show 0 ≤ 4 * H by positivity)
    have he : (Q / (4 * H) - R / 2) * (4 * H) = Q - 2 * H * R := by
      field_simp
      ring
    rw [he] at h
    simpa only [mul_comm G] using h
  exact internal_two_comparisons hH (bestSwapGain_nonneg q u i) h1 h2

/-- The right child's right action gains one level of bonus on its right
subtree when the child switches there. -/
theorem internal_right_child_second {h M U N T : ℕ} (e : Fin N ≃ TreeAction h M U)
    (v : TreeNode h) (hv : (v.1 : ℕ) + 1 < h) (side : Bool)
    (active : ℕ → Fin (2 ^ h)) (coin : TreeNode h → Bool) (leafCoin : ℕ → Bool)
    (selected : Fin (2 ^ h) → Fin M) (q : ℕ → Fin N → ℝ)
    (hq : ∀ t < T, ∀ i, 0 ≤ q t i) :
    let i := e.symm (.inl (v, side))
    let w := v.child (by omega) true
    let u (t : ℕ) (j : Fin N) := treeBonusProb (active t) coin (leafCoin t) (selected (active t)) (e j)
    let c := 1 / (2 * treeHeight h)
    (∑ t ∈ Finset.range T, q t i *
      (if w.active (active t) ∧ w.mid ≤ (active t : ℕ) ∧ coin w = true then c
       else if w.active (active t) ∨ (v.active (active t) ∧ side = false) then -(1 / 2)
       else 0)) ≤ bestSwapGain T q u i := by
  intro i w u c
  have hd : (v.1 : ℕ) < h := by omega
  have hw : (w.1 : ℕ) < h := hv
  have hH : 0 < treeHeight h := by unfold treeHeight; positivity
  let d : ℝ := ((v.1 : ℕ) : ℝ) + 1
  let dw : ℝ := ((w.1 : ℕ) : ℝ) + 1
  have he : dw = d + 1 := by simp [dw, d, w, TreeNode.child]
  have hfrac : d / (2 * treeHeight h) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    dsimp [d, treeHeight]
    have hdepth : ((v.1 : ℕ) : ℝ) ≤ h := by exact_mod_cast hd.le
    linarith
  have hdiff : dw / (2 * treeHeight h) - d / (2 * treeHeight h) = c := by
    rw [← sub_div, he, add_sub_cancel_left]
  let j := e.symm (.inl (w, true))
  apply weighted_gain_bound q u i j _ (fun t ht => hq t ht i)
  intro t _
  have hsource : u t i ≤ d / (2 * treeHeight h) := by
    simp only [u, i, Equiv.apply_symm_apply, treeBonusProb, hd.ne, if_false]
    split_ifs <;> first | exact le_rfl | (unfold d; positivity)
  have hj : 0 ≤ u t j := (treeBonusProb_mem _ _ _ _ _).1
  by_cases hr : w.active (active t) ∧ w.mid ≤ (active t : ℕ) ∧ coin w = true
  · have htarget : u t j = dw / (2 * treeHeight h) := by
      simp [u, j, treeBonusProb, hr.1, hw.ne, not_lt_of_ge hr.2.1, hr.2.2, dw]
    rw [if_pos hr, ← hdiff, htarget]
    exact sub_le_sub_left hsource _
  · rw [if_neg hr]
    by_cases hx : w.active (active t) ∨ (v.active (active t) ∧ side = false)
    · rw [if_pos hx]
      linarith only [hsource.trans hfrac, hj]
    · rw [if_neg hx]
      have hzero : u t i = 0 := by
        by_cases ha : v.active (active t)
        · have hside : side = true := by
            cases side
            · exact (hx (Or.inr ⟨ha, rfl⟩)).elim
            · rfl
          have hleft : (active t : ℕ) < v.mid := lt_of_not_ge fun hh =>
            hx (Or.inl ((v.child_active_iff hd (active t)).2.mpr ⟨ha, hh⟩))
          simp [u, i, treeBonusProb, ha, hd.ne, hside, hleft]
        · simp [u, i, treeBonusProb, ha]
      rw [hzero, sub_zero]
      exact hj

/-- Case 3 of Appendix D.1 after averaging over the finite uniform table
of internal-node coins. The play mass in the left subtree is causal. -/
theorem deepest_left_coin_sum {h M U N T : ℕ} (e : Fin N ≃ TreeAction h M U)
    (v : TreeNode h) (hv : (v.1 : ℕ) + 1 = h)
    (active : ℕ → Fin (2 ^ h)) (leafCoin : ℕ → Bool) (selected : Fin (2 ^ h) → Fin M)
    (q : (TreeNode h → Bool) → ℕ → Fin N → ℝ)
    (hq : ∀ c t, t < T → ∀ i, 0 ≤ q c t i) :
    let i := e.symm (.inl (v, false))
    let l := v.child (by omega) false
    let _r := v.child (by omega) true
    let L (c : TreeNode h → Bool) := ∑ t ∈ Finset.range T, if l.active (active t) then q c t i else 0
    let Q (c : TreeNode h → Bool) := ∑ t ∈ Finset.range T, q c t i
    let u (c : TreeNode h → Bool) (t : ℕ) (j : Fin N) :=
      treeBonusProb (active t) c (leafCoin t) (selected (active t)) (e j)
    (∀ c b, L (Function.update c v b) = L c) →
      (∑ c, Q c) / (184 * treeHeight h ^ 5) ≤ ∑ c, bestSwapGain T (q c) (u c) i := by
  intro i l r L Q u hL
  let R (c : TreeNode h → Bool) := ∑ t ∈ Finset.range T, if r.active (active t) then q c t i else 0
  let G (c : TreeNode h → Bool) := bestSwapGain T (q c) (u c) i
  let H := treeHeight h
  have hH : 1 ≤ H := by dsimp [H, treeHeight]; linarith [Nat.cast_nonneg (α := ℝ) h]
  have hH' : 0 < H := zero_lt_one.trans_le hH
  have hd : (v.1 : ℕ) < h := by omega
  have hl_sum (c : TreeNode h → Bool) :
      (∑ t ∈ Finset.range T, q c t i * (if l.active (active t) then 1 / (2 * H) else 0)) =
        L c / (2 * H) := by
    unfold L
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun t _ => by split <;> simp [div_eq_mul_inv]
  have hsplit (c : TreeNode h → Bool) :
      (∑ t ∈ Finset.range T, if v.active (active t) then q c t i else 0) = L c + R c := by
    unfold L R
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    obtain ⟨hl, hr⟩ := v.child_active_iff hd (active t)
    by_cases ha : v.active (active t)
    · by_cases hb : (active t : ℕ) < v.mid
      · simp [l, r, hl, hr, ha, hb, not_le_of_gt hb]
      · simp [l, r, hl, hr, ha, hb, le_of_not_gt hb]
    · simp [l, r, hl, hr, ha]
  have h1' (c : TreeNode h → Bool) : (if c v = true then L c else 0) / (2 * H) ≤ G c := by
    by_cases hc : c v = true
    · rw [if_pos hc, ← hl_sum c]
      exact (deepest_left_comparisons e v hv active c leafCoin selected (q c) (hq c)).1 hc
    · simpa only [if_neg hc, zero_div] using bestSwapGain_nonneg (q c) (u c) i
  have h2' (c : TreeNode h → Bool) : R c / (2 * H) - L c / 2 ≤ G c := by
    have hh := (deepest_left_comparisons e v hv active c leafCoin selected (q c) (hq c)).2
    have he : (∑ t ∈ Finset.range T, q c t i *
        (if r.active (active t) then 1 / (2 * H) else if l.active (active t) then -(1 / 2) else 0)) =
        R c / (2 * H) - L c / 2 := by
      unfold R L
      rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun t _ => ?_
      by_cases hr : r.active (active t)
      · have hl : ¬ l.active (active t) := by
          intro hl
          exact (not_lt_of_ge ((v.child_active_iff hd (active t)).2.mp hr).2)
            ((v.child_active_iff hd (active t)).1.mp hl).2
        simp [hr, hl, div_eq_mul_inv]
      · by_cases hl : l.active (active t) <;> simp [hr, hl, div_eq_mul_inv]
    exact he ▸ hh
  have h3' (c : TreeNode h → Bool) : Q c / (4 * H) - (L c + R c) / 2 ≤ G c := by
    rw [← hsplit c]
    simpa only [Bool.false_eq_true, if_false] using
      internal_root_support_gain e v hd false active c leafCoin selected (q c) (hq c)
  let x := ∑ c, L c
  let y := ∑ c, R c
  let total := ∑ c, Q c
  let gain := ∑ c, G c
  have hE := sum_on_fair_coin v true L hL
  have hl : x / (4 * H) ≤ gain := by
    have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (TreeNode h → Bool))) fun c _ => h1' c
    rw [← Finset.sum_div, hE] at hh
    exact (show x / (4 * H) = (x / 2) / (2 * H) by ring).le.trans hh
  have hr : y / (2 * H) - x / 2 ≤ gain := by
    have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (TreeNode h → Bool))) fun c _ => h2' c
    simpa only [Finset.sum_sub_distrib, ← Finset.sum_div] using hh
  have hroot : total / (4 * H) - (x + y) / 2 ≤ gain := by
    have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (TreeNode h → Bool))) fun c _ => h3' c
    simpa only [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_add_distrib] using hh
  have hx : 0 ≤ x := by
    refine Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun t ht => ?_
    split
    · exact hq c t (Finset.mem_range.mp ht) i
    · rfl
  have hg : 0 ≤ gain := Finset.sum_nonneg fun c _ => bestSwapGain_nonneg (q c) (u c) i
  have h1 : 4 * H ^ 2 * x ≤ 16 * H ^ 3 * gain := by
    have hh := (div_le_iff₀ (show 0 < 4 * H by positivity)).mp hl
    nlinarith only [mul_le_mul_of_nonneg_left hh (show 0 ≤ 4 * H ^ 2 by positivity)]
  have h2 : 2 * H * y - 2 * H ^ 2 * x ≤ 4 * H ^ 2 * gain := by
    have hh := mul_le_mul_of_nonneg_right hr (show 0 ≤ 4 * H ^ 2 by positivity)
    have he : (y / (2 * H) - x / 2) * (4 * H ^ 2) = 2 * H * y - 2 * H ^ 2 * x := by
      field_simp; ring
    rw [he] at hh
    nlinarith only [hh]
  have h3 : total - 2 * H * (x + y) ≤ 4 * H * gain := by
    have hh := mul_le_mul_of_nonneg_right hroot (show 0 ≤ 4 * H by positivity)
    have he : (total / (4 * H) - (x + y) / 2) * (4 * H) = total - 2 * H * (x + y) := by
      field_simp; ring
    rw [he] at hh
    nlinarith only [hh]
  exact internal_three_comparisons (x₂ := 0) (x₃ := y) hH hg hx le_rfl
    (by simpa only [mul_zero, add_zero] using h1)
    (by simpa only [add_zero] using h2)
    (by simpa only [add_zero] using h3)

/-- The left-child comparisons for a left action above the deepest
internal level. The event on the parent coin kills its right-subtree bonus. -/
theorem internal_left_child_comparisons {h M U N T : ℕ} (e : Fin N ≃ TreeAction h M U)
    (v : TreeNode h) (hv : (v.1 : ℕ) + 1 < h)
    (active : ℕ → Fin (2 ^ h)) (coin : TreeNode h → Bool) (leafCoin : ℕ → Bool)
    (selected : Fin (2 ^ h) → Fin M) (q : ℕ → Fin N → ℝ)
    (hq : ∀ t < T, ∀ i, 0 ≤ q t i) :
    let i := e.symm (.inl (v, false))
    let w := v.child (by omega) false
    let u (t : ℕ) (j : Fin N) := treeBonusProb (active t) coin (leafCoin t) (selected (active t)) (e j)
    let c := 1 / (2 * treeHeight h)
    coin v = true →
      (coin w = false →
        (∑ t ∈ Finset.range T, q t i * (if w.active (active t) then c else 0)) ≤ bestSwapGain T q u i) ∧
      (∑ t ∈ Finset.range T, q t i *
        (if w.active (active t) ∧ w.mid ≤ (active t : ℕ) ∧ coin w = true then c
         else if w.active (active t) then -(1 / 2) else 0)) ≤ bestSwapGain T q u i := by
  intro i w u c hc
  have hd : (v.1 : ℕ) < h := by omega
  have hw : (w.1 : ℕ) < h := hv
  have hH : 0 < treeHeight h := by unfold treeHeight; positivity
  let d : ℝ := ((v.1 : ℕ) : ℝ) + 1
  let dw : ℝ := ((w.1 : ℕ) : ℝ) + 1
  have he : dw = d + 1 := by simp [dw, d, w, TreeNode.child]
  have hfrac : d / (2 * treeHeight h) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    dsimp [d, treeHeight]
    have hdepth : ((v.1 : ℕ) : ℝ) ≤ h := by exact_mod_cast hd.le
    linarith
  have hdiff : dw / (2 * treeHeight h) - d / (2 * treeHeight h) = c := by
    rw [← sub_div, he, add_sub_cancel_left]
  have hsource (t : ℕ) : u t i = if w.active (active t) then d / (2 * treeHeight h) else 0 := by
    have ha : w.active (active t) ↔ v.active (active t) ∧ (active t : ℕ) < v.mid :=
      (v.child_active_iff hd (active t)).1
    by_cases ht : v.active (active t)
    · by_cases hl : (active t : ℕ) < v.mid
      · have hwa := ha.mpr ⟨ht, hl⟩
        simp [u, i, treeBonusProb, ht, hd.ne, hl, d, hwa]
      · have hnwa : ¬ w.active (active t) := fun hh => hl (ha.mp hh).2
        simp [u, i, treeBonusProb, ht, hd.ne, hl, hc, hnwa]
    · have hnwa : ¬ w.active (active t) := fun hh => ht (ha.mp hh).1
      simp [u, i, treeBonusProb, ht, hnwa]
  constructor
  · intro hwc
    apply weighted_gain_bound q u i (e.symm (.inl (w, false))) _ (fun t ht => hq t ht i)
    intro t _
    rw [hsource t]
    by_cases hr : w.active (active t)
    · have htarget : u t (e.symm (.inl (w, false))) = dw / (2 * treeHeight h) := by
        by_cases hl : (active t : ℕ) < w.mid <;> simp [u, treeBonusProb, hr, hw.ne, hl, hwc, dw]
      rw [htarget]
      simp only [if_pos hr, hdiff]
      exact le_rfl
    · simp [u, treeBonusProb, hr]
  · let j := e.symm (.inl (w, true))
    apply weighted_gain_bound q u i j _ (fun t ht => hq t ht i)
    intro t _
    rw [hsource t]
    by_cases hr : w.active (active t)
    · by_cases hd' : w.mid ≤ (active t : ℕ) ∧ coin w = true
      · have htarget : u t j = dw / (2 * treeHeight h) := by
          simp [u, j, treeBonusProb, hr, hw.ne, not_lt_of_ge hd'.1, hd'.2, dw]
        rw [if_pos ⟨hr, hd'⟩, if_pos hr, htarget, hdiff]
      · have hj : 0 ≤ u t j := (treeBonusProb_mem _ _ _ _ _).1
        rw [if_neg (fun h => hd' h.2), if_pos hr, if_pos hr]
        linarith only [hfrac, hj]
    · simp [u, j, treeBonusProb, hr]

/-- Mass in a subtree splits into the two child masses. -/
theorem sum_child_mass {h T : ℕ} (w : TreeNode h) (hw : (w.1 : ℕ) < h)
    (active : ℕ → Fin (2 ^ h)) (p : ℕ → ℝ) :
    (∑ t ∈ Finset.range T, if w.active (active t) then p t else 0) =
      (∑ t ∈ Finset.range T, if (w.child hw false).active (active t) then p t else 0) +
      (∑ t ∈ Finset.range T, if (w.child hw true).active (active t) then p t else 0) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  obtain ⟨hl, hr⟩ := w.child_active_iff hw (active t)
  by_cases ha : w.active (active t)
  · by_cases ht : (active t : ℕ) < w.mid
    · simp [hl, hr, ha, ht, not_le_of_gt ht]
    · simp [hl, hr, ha, ht, le_of_not_gt ht]
  · simp [hl, hr, ha]

/-- Left subtrees finish before the midpoint of the parent and before the
midpoint of its right child. Right subtrees finish at their parent's end. -/
theorem child_timing {h : ℕ} (w : TreeNode h) (hw : (w.1 : ℕ) < h) :
    (w.child hw false).last = w.mid ∧
    (w.child hw true).first = w.mid ∧
    (w.child hw true).last = w.last ∧
    (w.child hw false).mid ≤ w.mid ∧
    w.mid ≤ (w.child hw true).mid := by
  obtain ⟨_, hl, hr, he⟩ := w.child_edges hw
  have hmid (j : TreeNode h) : j.first ≤ j.mid ∧ j.mid ≤ j.last := by
    unfold TreeNode.mid TreeNode.last TreeNode.first
    rw [Nat.add_mul, one_mul]
    exact ⟨Nat.le_add_right _ _, Nat.add_le_add_left (Nat.pow_le_pow_right (by decide) (by omega)) _⟩
  exact ⟨hl, hr, he, (hmid _).2.trans_eq hl, hr.symm.trans_le (hmid _).1⟩

/-- If the weight is unchanged when a coin is updated, a gate on a distinct
coin can be included in that weight before summing over the first coin. -/
theorem sum_on_two_coins {ι : Type*} [Fintype ι] [DecidableEq ι]
    (j k : ι) (hjk : k ≠ j) (b d : Bool) (g : (ι → Bool) → ℝ)
    (hg : ∀ c v, g (Function.update c j v) = g c) :
    (∑ c : ι → Bool, if c j = b ∧ c k = d then g c else 0) =
      (∑ c, if c k = d then g c else 0) / 2 := by
  let f (c : ι → Bool) := if c k = d then g c else 0
  have hf (c : ι → Bool) (v : Bool) : f (Function.update c j v) = f c := by
    simp only [f, Function.update_of_ne hjk, hg c v]
  have hh := sum_on_fair_coin j b f hf
  simpa only [f, ite_and] using hh

/-- Current leaf coin is invisible when the learner chooses its current action. -/
theorem feedbackHistory_update_leafCoin {h M U T : ℕ}
    (pick : (t : ℕ) → FeedbackHistory t → TreeAction h M U)
    (active : ℕ → Fin (2 ^ h)) (η : ℝ) (coin : TreeNode h → Bool)
    (c : Fin T → Bool) (selected : Fin (2 ^ h) → Fin M)
    (z : ℕ → Icc (0 : ℝ) 1) (draw : ℕ → TreeAction h M U → Ico (0 : ℝ) 1)
    (t : Fin T) (b : Bool) :
    let payoff (c' : Fin T → Bool) (s : ℕ) :=
      treeReward η (active s) coin (if hs : s < T then c' ⟨s, hs⟩ else false)
        (selected (active s)) (z s) (draw s)
    feedbackHistory pick (payoff (Function.update c t b)) t =
      feedbackHistory pick (payoff c) t := by
  intro payoff
  apply feedbackHistory_eq_of_prior_rewards_eq
  intro s hs a
  have hs' : s < T := hs.trans t.isLt
  have hne : (⟨s, hs'⟩ : Fin T) ≠ t := fun hh => hs.ne (congrArg Fin.val hh)
  simp only [payoff, dif_pos hs', Function.update_of_ne hne]

/-- A leaf action accounts for its full expected play mass up to the factor
(8H); either it is played in the active period or the root pair gains. -/
theorem leaf_coin_sum {h M U N T : ℕ} (hh : 0 < h)
    (e : Fin N ≃ TreeAction h M U) (v : TreeNode h) (hv : (v.1 : ℕ) = h) (side : Bool)
    (active : ℕ → Fin (2 ^ h)) (coin : TreeNode h → Bool)
    (selected : Fin (2 ^ h) → Fin M) (q : (Fin T → Bool) → ℕ → Fin N → ℝ)
    (hq : ∀ c t, t < T → ∀ i, 0 ≤ q c t i)
    (hcausal : ∀ (c : Fin T → Bool) (t : Fin T) b i, q (Function.update c t b) t i = q c t i) :
    let i := e.symm (.inl (v, side))
    let u (c : Fin T → Bool) (t : ℕ) (j : Fin N) :=
      treeBonusProb (active t) coin (if ht : t < T then c ⟨t, ht⟩ else false) (selected (active t)) (e j)
    (∑ c, ∑ t ∈ Finset.range T, q c t i) / (8 * treeHeight h) ≤
      ∑ c, bestSwapGain T (q c) (u c) i := by
  classical
  intro i u
  let period := (Finset.range T).filter fun t => v.active (active t)
  let leafAt : Fin (2 ^ h) := ⟨v.2, by simpa only [hv] using v.2.isLt⟩
  let aux := e.symm (.inr (.inl (selected leafAt)))
  let rootA := e.symm (.inl (TreeNode.root h, false))
  let rootB := e.symm (.inl (TreeNode.root h, true))
  have hp : period ⊆ Finset.range T := Finset.filter_subset _ _
  have hcomp (c : Fin T → Bool) :=
    leaf_bestSwapGain (q c) (u c) period hp i aux rootA rootB (treeHeight h)
      (fun t ht => hq c t ht i)
      (fun t _ => (treeBonusProb_mem _ _ _ _ _).1)
      (fun t ht hnot => by
        have hna : ¬v.active (active t) := fun ha => hnot (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ht, ha⟩)
        simp [u, i, treeBonusProb, hna])
      (fun t ht => by
        have hact := (Finset.mem_filter.mp ht).2
        have heq : active t = leafAt := Fin.ext ((v.active_leaf_iff hv _).mp hact)
        simp [u, aux, treeBonusProb, heq])
      (fun t _ => by
        simpa only [u, rootA, rootB, Equiv.apply_symm_apply] using
          treeBonusProb_root_pair (U := U) hh (active t) coin
            (if ht : t < T then c ⟨t, ht⟩ else false) (selected (active t)))
  have hon (t : ℕ) (ht : t ∈ period) :
      (∑ c : Fin T → Bool, q c t i * u c t i) = (∑ c, q c t i) / 2 := by
    obtain ⟨ht', hact⟩ := Finset.mem_filter.mp ht
    have hlt := Finset.mem_range.mp ht'
    let j : Fin T := ⟨t, hlt⟩
    have hj (c : Fin T → Bool) :
        q c t i * u c t i = if c j = side then q c t i else 0 := by
      by_cases hc : c j = side
      · simp [u, i, treeBonusProb, hact, hv, hlt, ← hc, j]
      · have hn : side ≠ c j := Ne.symm hc
        simp [u, i, treeBonusProb, hact, hv, hlt, hc, hn, j]
    simp_rw [hj]
    exact sum_on_fair_coin j side (fun c => q c t i) (fun c b => hcausal c j b i)
  have he :
      (∑ c : Fin T → Bool, ∑ t ∈ period, q c t i * u c t i) =
        (∑ c : Fin T → Bool, ∑ t ∈ period, q c t i) / 2 := calc
    _ = ∑ t ∈ period, ∑ c : Fin T → Bool, q c t i * u c t i := Finset.sum_comm
    _ = ∑ t ∈ period, (∑ c : Fin T → Bool, q c t i) / 2 :=
      Finset.sum_congr rfl hon
    _ = _ := by rw [← Finset.sum_div, Finset.sum_comm]
  have h₁ : (∑ c : Fin T → Bool, ∑ t ∈ period, q c t i) / 2 ≤
      ∑ c, bestSwapGain T (q c) (u c) i := by
    have hc := Finset.sum_le_sum (s := Finset.univ) fun c _ => (hcomp c).1
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, he] at hc
    linarith only [hc]
  have h₂ : (∑ c : Fin T → Bool, ∑ t ∈ Finset.range T, q c t i) / (4 * treeHeight h) -
      (∑ c : Fin T → Bool, ∑ t ∈ period, q c t i) / 2 ≤
      ∑ c, bestSwapGain T (q c) (u c) i := by
    have hc := Finset.sum_le_sum (s := Finset.univ) fun c _ => (hcomp c).2
    simpa only [Finset.sum_sub_distrib, ← Finset.sum_div, he] using hc
  exact leaf_expected_gain h₁ h₂

/-- When the learner's seed is fixed, its distribution for a round is
concentrated on the action it chooses from the preceding feedback. -/
noncomputable def treePlayProbability {h M U N : ℕ} (e : Fin N ≃ TreeAction h M U)
    (pick : (t : ℕ) → FeedbackHistory t → TreeAction h M U)
    (active : ℕ → Fin (2 ^ h)) (η : ℝ) (coin : TreeNode h → Bool) (leafCoin : ℕ → Bool)
    (selected : Fin (2 ^ h) → Fin M) (z : ℕ → Icc (0 : ℝ) 1)
    (draw : ℕ → TreeAction h M U → Ico (0 : ℝ) 1) (t : ℕ) (i : Fin N) : ℝ :=
  let y (s : ℕ) := treeReward η (active s) coin (leafCoin s) (selected (active s)) (z s) (draw s)
  if pick t (feedbackHistory pick y t) = e i then 1 else 0

theorem treePlayProbability_isProbVec {h M U N : ℕ} (e : Fin N ≃ TreeAction h M U)
    (pick : (t : ℕ) → FeedbackHistory t → TreeAction h M U)
    (active : ℕ → Fin (2 ^ h)) (η : ℝ) (coin : TreeNode h → Bool) (leafCoin : ℕ → Bool)
    (selected : Fin (2 ^ h) → Fin M) (z : ℕ → Icc (0 : ℝ) 1)
    (draw : ℕ → TreeAction h M U → Ico (0 : ℝ) 1) (t : ℕ) :
    IsProbVec (treePlayProbability e pick active η coin leafCoin selected z draw t) := by
  classical
  unfold treePlayProbability
  dsimp only
  constructor
  · intro i
    dsimp only
    split <;> norm_num
  · let y (s : ℕ) := treeReward η (active s) coin (leafCoin s) (selected (active s)) (z s) (draw s)
    let a := pick t (feedbackHistory pick y t)
    change (∑ i, if a = e i then (1 : ℝ) else 0) = 1
    have he (i : Fin N) : a = e i ↔ i = e.symm a := by
      constructor
      · intro he
        rw [he, Equiv.symm_apply_apply]
      · rintro rfl
        rw [Equiv.apply_symm_apply]
    simp [he]

/-- The conditional subtree masses used in the swap comparisons are
causal for the actual fixed-seed policy. -/
theorem treePlayProbability_subtree_independent {h M U N T : ℕ}
    (e : Fin N ≃ TreeAction h M U) (pick : (t : ℕ) → FeedbackHistory t → TreeAction h M U)
    (active : ℕ → Fin (2 ^ h)) (ha : Monotone active)
    (w v : TreeNode h) (hbefore : w.last ≤ v.mid) (η : ℝ)
    (coin : TreeNode h → Bool) (leafCoin : ℕ → Bool)
    (selected : Fin (2 ^ h) → Fin M) (z : ℕ → Icc (0 : ℝ) 1)
    (draw : ℕ → TreeAction h M U → Ico (0 : ℝ) 1) (i : Fin N) (b : Bool) :
    let Q (c : TreeNode h → Bool) := ∑ t ∈ Finset.range T,
      if w.active (active t) then treePlayProbability e pick active η c leafCoin selected z draw t i else 0
    Q (Function.update coin v b) = Q coin := by
  intro Q
  have he (c : TreeNode h → Bool) :
      Q c = subtreePlayMass pick active w η c leafCoin selected z draw T (e i) := by
    unfold Q treePlayProbability subtreePlayMass
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases ht : w.active (active t) <;> simp [ht]
  rw [he, he]
  exact subtreePlayMass_update_of_before pick active ha w v hbefore
    η coin leafCoin selected z draw T (e i) b

/-- Case 2 of Appendix D.1. Only play mass in the first grandchild is
independent of the right child's coin, which is revealed later. -/
theorem internal_right_coin_sum {h M U N T : ℕ} (e : Fin N ≃ TreeAction h M U)
    (v : TreeNode h) (hv : (v.1 : ℕ) + 1 < h) (active : ℕ → Fin (2 ^ h))
    (leafCoin : ℕ → Bool) (selected : Fin (2 ^ h) → Fin M)
    (q : (TreeNode h → Bool) → ℕ → Fin N → ℝ)
    (hq : ∀ c t, t < T → ∀ i, 0 ≤ q c t i) :
    let i := e.symm (.inl (v, true))
    let w := v.child (by omega) true
    let l := w.child hv false
    let L (c : TreeNode h → Bool) := ∑ t ∈ Finset.range T, if l.active (active t) then q c t i else 0
    let u (c : TreeNode h → Bool) (t : ℕ) (j : Fin N) :=
      treeBonusProb (active t) c (leafCoin t) (selected (active t)) (e j)
    (∀ c b, L (Function.update c w b) = L c) →
    (∑ c, ∑ t ∈ Finset.range T, q c t i) / (184 * treeHeight h ^ 5) ≤
      ∑ c, bestSwapGain T (q c) (u c) i := by
  classical
  intro i w l L u hL
  let r := w.child hv true
  let R (c : TreeNode h → Bool) := ∑ t ∈ Finset.range T, if r.active (active t) then q c t i else 0
  let W (c : TreeNode h → Bool) := ∑ t ∈ Finset.range T, if w.active (active t) then q c t i else 0
  let G (c : TreeNode h → Bool) := bestSwapGain T (q c) (u c) i
  let H := treeHeight h
  have hH : 1 ≤ H := by dsimp [H, treeHeight]; linarith only [Nat.cast_nonneg (α := ℝ) h]
  let x₁ := ∑ c, L c
  let x₂ := ∑ c, if c w = false then R c else 0
  let x₃ := ∑ c, if c w = true then R c else 0
  have hsplit (c : TreeNode h → Bool) : W c = L c + R c :=
    sum_child_mass w hv active (fun t => q c t i)
  have hRsum : (∑ c, R c) = x₂ + x₃ := by
    dsimp only [x₂, x₃]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => by cases c w <;> simp
  have hWsum : (∑ c, W c) = x₁ + x₂ + x₃ := by
    simp_rw [hsplit, Finset.sum_add_distrib, hRsum]
    ring
  have h₁ : x₂ / (2 * H) + x₁ / (4 * H) ≤ ∑ c, G c := by
    have hh (c : TreeNode h → Bool) :
        (if c w = false then W c / (2 * H) else 0) ≤ G c := by
      by_cases hc : c w = false
      · rw [if_pos hc]
        have h := internal_right_child_first e v hv true active c leafCoin selected (q c) (hq c) hc
        convert h using 1
        unfold W H
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro t _
        by_cases ht : w.active (active t)
        · simp [ht, w]
          ring
        · simp [ht, w]
      · rw [if_neg hc]
        exact bestSwapGain_nonneg (q c) (u c) i
    have hsum := Finset.sum_le_sum (s := Finset.univ) fun c _ => hh c
    have hs : (∑ c, if c w = false then W c / (2 * H) else 0) =
        x₂ / (2 * H) + x₁ / (4 * H) := by
      have hg (c : TreeNode h → Bool) :
          (if c w = false then W c / (2 * H) else 0) =
          (if c w = false then L c else 0) / (2 * H) +
          (if c w = false then R c else 0) / (2 * H) := by
        by_cases hc : c w = false
        · simp only [hc, if_true, hsplit, add_div]
        · simp [hc]
      rw [Finset.sum_congr rfl (fun c _ => hg c), Finset.sum_add_distrib,
        ← Finset.sum_div, ← Finset.sum_div, sum_on_fair_coin w false L hL]
      change (x₁ / 2) / (2 * H) + x₂ / (2 * H) = _
      ring
    rwa [hs] at hsum
  have h₂ : x₃ / (2 * H) - (x₁ + x₂) / 2 ≤ ∑ c, G c := by
    have hh (c : TreeNode h → Bool) :
        (if c w = true then R c / (2 * H) else -R c / 2) - L c / 2 ≤ G c := by
      have hp := internal_right_child_second e v hv true active c leafCoin selected (q c) (hq c)
      have he :
          (if c w = true then R c / (2 * H) else -R c / 2) - L c / 2 =
            ∑ t ∈ Finset.range T, q c t i *
              (if w.active (active t) ∧ w.mid ≤ (active t : ℕ) ∧ c w = true then 1 / (2 * H)
               else if w.active (active t) then -(1 / 2) else 0) := by
        have hm (t : ℕ) := w.child_active_iff hv (active t)
        by_cases hc : c w = true
        · rw [if_pos hc]
          unfold R L
          rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun t _ => ?_
          simp only [r, l, (hm t).1, (hm t).2]
          by_cases ha : w.active (active t)
          · by_cases he : (active t : ℕ) < w.mid
            · simp [ha, he, not_le_of_gt he]; ring
            · simp [hc, ha, he, le_of_not_gt he]; ring
          · simp [ha]
        · rw [if_neg hc]
          unfold R L
          rw [← Finset.sum_neg_distrib, Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun t _ => ?_
          simp only [r, l, (hm t).1, (hm t).2]
          by_cases ha : w.active (active t)
          · by_cases he : (active t : ℕ) < w.mid
            · simp [ha, he, not_le_of_gt he, hc]; ring
            · simp [ha, he, le_of_not_gt he, hc]; ring
          · simp [ha]
      rw [he]
      simpa only [w, i, u, H, Bool.true_eq_false, and_false, or_false] using hp
    have hsum := Finset.sum_le_sum (s := Finset.univ) fun c _ => hh c
    have hs (c : TreeNode h → Bool) :
        (if c w = true then R c / (2 * H) else -R c / 2) - L c / 2 =
          (if c w = true then R c else 0) / (2 * H) -
          ((if c w = false then R c else 0) + L c) / 2 := by
      cases c w
      · simp
        ring
      · simp
    rw [Finset.sum_congr rfl (fun c _ => hs c), Finset.sum_sub_distrib,
      ← Finset.sum_div, ← Finset.sum_div, Finset.sum_add_distrib] at hsum
    change x₃ / (2 * H) - (x₂ + x₁) / 2 ≤ ∑ c, G c at hsum
    rwa [add_comm x₁ x₂]
  have h₃ : (∑ c, ∑ t ∈ Finset.range T, q c t i) / (4 * H) -
      (x₁ + x₂ + x₃) / 2 ≤ ∑ c, G c := by
    have hh (c : TreeNode h → Bool) :
        (∑ t ∈ Finset.range T, q c t i) / (4 * H) - W c / 2 ≤ G c :=
      internal_root_support_gain e v (by omega) true active c leafCoin selected (q c) (hq c)
    have hsum := Finset.sum_le_sum (s := Finset.univ) fun c _ => hh c
    simpa only [Finset.sum_sub_distrib, ← Finset.sum_div, hWsum] using hsum
  have hLn : ∀ c, 0 ≤ L c := fun c => Finset.sum_nonneg fun t ht => by
    split
    · exact hq c t (Finset.mem_range.mp ht) i
    · exact le_rfl
  have hRn : ∀ c, 0 ≤ R c := fun c => Finset.sum_nonneg fun t ht => by
    split
    · exact hq c t (Finset.mem_range.mp ht) i
    · exact le_rfl
  exact internal_right_gain_of_comparisons hH
    (Finset.sum_nonneg fun c _ => bestSwapGain_nonneg (q c) (u c) i)
    (Finset.sum_nonneg fun c _ => hLn c)
    (Finset.sum_nonneg fun c _ => by split; exact hRn c; exact le_rfl) h₁ h₂ h₃

/-- The right action of a node above the deepest internal level satisfies
its averaged comparison for the actual learner with a fixed seed. -/
theorem internal_right_coin_sum_policy {h M U N T : ℕ} (e : Fin N ≃ TreeAction h M U)
    (v : TreeNode h) (hv : (v.1 : ℕ) + 1 < h)
    (pick : (t : ℕ) → FeedbackHistory t → TreeAction h M U)
    (active : ℕ → Fin (2 ^ h)) (ha : Monotone active) (η : ℝ) (leafCoin : ℕ → Bool)
    (selected : Fin (2 ^ h) → Fin M) (z : ℕ → Icc (0 : ℝ) 1)
    (draw : ℕ → TreeAction h M U → Ico (0 : ℝ) 1) :
    let i := e.symm (.inl (v, true))
    let q (coin : TreeNode h → Bool) := treePlayProbability e pick active η coin leafCoin selected z draw
    let u (coin : TreeNode h → Bool) (t : ℕ) (j : Fin N) :=
      treeBonusProb (active t) coin (leafCoin t) (selected (active t)) (e j)
    (∑ c, ∑ t ∈ Finset.range T, q c t i) / (184 * treeHeight h ^ 5) ≤
      ∑ c, bestSwapGain T (q c) (u c) i := by
  intro i q u
  refine internal_right_coin_sum e v hv active leafCoin selected q (fun c t _ j => ?_) ?_
  · exact (treePlayProbability_isProbVec e pick active η c leafCoin selected z draw t).1 j
  · intro c b
    let w := v.child (by omega) true
    exact treePlayProbability_subtree_independent e pick active ha (w.child hv false) w
      (w.child_edges hv).2.1.le η c leafCoin selected z draw i b

/-- Case 3 of Appendix D.1 for the actual learner with a fixed seed. -/
theorem deepest_left_coin_sum_policy {h M U N T : ℕ} (e : Fin N ≃ TreeAction h M U)
    (v : TreeNode h) (hv : (v.1 : ℕ) + 1 = h)
    (pick : (t : ℕ) → FeedbackHistory t → TreeAction h M U)
    (active : ℕ → Fin (2 ^ h)) (ha : Monotone active) (η : ℝ) (leafCoin : ℕ → Bool)
    (selected : Fin (2 ^ h) → Fin M) (z : ℕ → Icc (0 : ℝ) 1)
    (draw : ℕ → TreeAction h M U → Ico (0 : ℝ) 1) :
    let i := e.symm (.inl (v, false))
    let q (coin : TreeNode h → Bool) := treePlayProbability e pick active η coin leafCoin selected z draw
    let u (coin : TreeNode h → Bool) (t : ℕ) (j : Fin N) :=
      treeBonusProb (active t) coin (leafCoin t) (selected (active t)) (e j)
    (∑ c, ∑ t ∈ Finset.range T, q c t i) / (184 * treeHeight h ^ 5) ≤
      ∑ c, bestSwapGain T (q c) (u c) i := by
  intro i q u
  refine deepest_left_coin_sum e v hv active leafCoin selected q (fun c t _ j => ?_) ?_
  · exact (treePlayProbability_isProbVec e pick active η c leafCoin selected z draw t).1 j
  · intro c b
    let hd : (v.1 : ℕ) < h := by omega
    exact treePlayProbability_subtree_independent e pick active ha (v.child hd false) v
      (v.child_edges hd).2.1.le η c leafCoin selected z draw i b

/-- The averaged leaf comparison for the actual learner with a fixed seed. -/
theorem leaf_coin_sum_policy {h M U N T : ℕ} (hh : 0 < h) (e : Fin N ≃ TreeAction h M U)
    (v : TreeNode h) (hv : (v.1 : ℕ) = h) (side : Bool)
    (pick : (t : ℕ) → FeedbackHistory t → TreeAction h M U)
    (active : ℕ → Fin (2 ^ h)) (η : ℝ) (coin : TreeNode h → Bool)
    (selected : Fin (2 ^ h) → Fin M) (z : ℕ → Icc (0 : ℝ) 1)
    (draw : ℕ → TreeAction h M U → Ico (0 : ℝ) 1) :
    let leafCoin (c : Fin T → Bool) (t : ℕ) := if ht : t < T then c ⟨t, ht⟩ else false
    let i := e.symm (.inl (v, side))
    let q (c : Fin T → Bool) := treePlayProbability e pick active η coin (leafCoin c) selected z draw
    let u (c : Fin T → Bool) (t : ℕ) (j : Fin N) :=
      treeBonusProb (active t) coin (leafCoin c t) (selected (active t)) (e j)
    (∑ c, ∑ t ∈ Finset.range T, q c t i) / (8 * treeHeight h) ≤
      ∑ c, bestSwapGain T (q c) (u c) i := by
  intro leafCoin i q u
  refine leaf_coin_sum hh e v hv side active coin selected q (fun c t _ j => ?_) ?_
  · exact (treePlayProbability_isProbVec e pick active η coin (leafCoin c) selected z draw t).1 j
  · intro c t b j
    have he := feedbackHistory_update_leafCoin pick active η coin c selected z draw t b
    dsimp only at he
    unfold q treePlayProbability leafCoin
    dsimp only
    rw [he]

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open Set

/-- Play mass of one action during the visits to a subtree. -/
private noncomputable def visitMass {h T : ℕ} (active : ℕ → Fin (2 ^ h)) (p : ℕ → ℝ)
    (v : TreeNode h) : ℝ :=
  ∑ t ∈ Finset.range T, if v.active (active t) then p t else 0

private theorem visitMass_nonneg {h T : ℕ} (active : ℕ → Fin (2 ^ h)) (p : ℕ → ℝ)
    (hp : ∀ t < T, 0 ≤ p t) (v : TreeNode h) :
    0 ≤ visitMass (T := T) active p v :=
  Finset.sum_nonneg fun t ht => by
    split
    · exact hp t (Finset.mem_range.mp ht)
    · exact le_rfl

private theorem visitMass_split {h T : ℕ} (active : ℕ → Fin (2 ^ h)) (p : ℕ → ℝ)
    (v : TreeNode h) (hv : (v.1 : ℕ) < h) :
    visitMass (T := T) active p v =
      visitMass (T := T) active p (v.child hv false) + visitMass (T := T) active p (v.child hv true) :=
  sum_child_mass v hv active p

private theorem visitMass_weight {h T : ℕ} (active : ℕ → Fin (2 ^ h)) (p : ℕ → ℝ)
    (v : TreeNode h) (a : ℝ) :
    (∑ t ∈ Finset.range T, p t * (if v.active (active t) then a else 0)) =
      visitMass (T := T) active p v * a := by
  rw [visitMass, Finset.sum_mul]
  exact Finset.sum_congr rfl fun t _ => by split <;> simp [*]

/-- Expand the left-action comparison within an internal child's subtree. -/
private theorem visitMass_child_switch {h T : ℕ} (active : ℕ → Fin (2 ^ h)) (p : ℕ → ℝ)
    (v : TreeNode h) (hv : (v.1 : ℕ) < h) (b : Bool) (a : ℝ) :
    (∑ t ∈ Finset.range T, p t *
      (if v.active (active t) ∧ v.mid ≤ (active t : ℕ) ∧ b = true then a
       else if v.active (active t) then -(1 / 2) else 0)) =
      (if b = true then visitMass (T := T) active p (v.child hv true) else 0) * a -
      ((if b = false then visitMass (T := T) active p (v.child hv true) else 0) +
        visitMass (T := T) active p (v.child hv false)) / 2 := by
  cases b
  · simp only [Bool.false_eq_true, and_false, if_false, if_true]
    rw [visitMass_weight, visitMass_split active p v hv]
    ring
  · simp only [Bool.true_eq_false, and_true, if_true, if_false, zero_add]
    unfold visitMass
    rw [Finset.sum_mul, Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    obtain ⟨hl, hr⟩ := v.child_active_iff hv (active t)
    by_cases hactive : v.active (active t)
    · by_cases hleft : (active t : ℕ) < v.mid
      · simp [hl, hr, hactive, hleft, not_le_of_gt hleft]
        ring
      · simp [hl, hr, hactive, hleft, le_of_not_gt hleft]
    · simp [hl, hr, hactive]

private theorem visitMass_compare_right {h T : ℕ} (active : ℕ → Fin (2 ^ h)) (p : ℕ → ℝ)
    (v : TreeNode h) (hv : (v.1 : ℕ) < h) (a : ℝ) :
    (∑ t ∈ Finset.range T, p t *
      (if (v.child hv true).active (active t) then a
       else if v.active (active t) then -(1 / 2) else 0)) =
      visitMass (T := T) active p (v.child hv true) * a -
        visitMass (T := T) active p (v.child hv false) / 2 := by
  unfold visitMass
  rw [Finset.sum_mul, Finset.sum_div, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  obtain ⟨hl, hr⟩ := v.child_active_iff hv (active t)
  by_cases hactive : v.active (active t)
  · by_cases hleft : (active t : ℕ) < v.mid
    · simp [hl, hr, hactive, hleft, not_le_of_gt hleft]
      ring
    · simp [hl, hr, hactive, hleft, le_of_not_gt hleft]
  · simp [hl, hr, hactive]

private theorem visitMass_compare_right_switch {h T : ℕ} (active : ℕ → Fin (2 ^ h)) (p : ℕ → ℝ)
    (v : TreeNode h) (hv : (v.1 : ℕ) < h) (w : TreeNode h) (hw : w = v.child hv true)
    (hv' : (w.1 : ℕ) < h) (b : Bool) (a : ℝ) :
    (∑ t ∈ Finset.range T, p t *
      (if w.active (active t) ∧ w.mid ≤ (active t : ℕ) ∧ b = true then a
       else if w.active (active t) ∨ v.active (active t) then -(1 / 2) else 0)) =
      (if b = true then visitMass (T := T) active p (w.child hv' true) else 0) * a -
      ((if b = false then visitMass (T := T) active p (w.child hv' true) else 0) +
        visitMass (T := T) active p (w.child hv' false) +
        visitMass (T := T) active p (v.child hv false)) / 2 := by
  subst w
  let w := v.child hv true
  have hs :=
    visitMass_child_switch (T := T) active p w hv' b a
  calc
    _ = (∑ t ∈ Finset.range T, p t *
          (if w.active (active t) ∧ w.mid ≤ (active t : ℕ) ∧ b = true then a
           else if w.active (active t) then -(1 / 2) else 0)) -
          visitMass (T := T) active p (v.child hv false) / 2 := by
      rw [visitMass, Finset.sum_div, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun t _ => ?_
      obtain ⟨hl, hr⟩ := v.child_active_iff hv (active t)
      by_cases hactive : v.active (active t)
      · by_cases hleft : (active t : ℕ) < v.mid
        · have hright : ¬ w.active (active t) := fun ht => (not_le_of_gt hleft) (hr.mp ht).2
          simp [hl, hactive, hleft, hright, w]
          ring
        · have hright : w.active (active t) := hr.mpr ⟨hactive, le_of_not_gt hleft⟩
          simp only [hl, hactive, hleft, and_false, if_false, hright, or_true, if_true,
            zero_div, sub_zero, w]
      · have hright : ¬ w.active (active t) := fun ht => hactive (hr.mp ht).1
        simp [hl, hactive, hright, w]
    _ = _ := by
      rw [hs]
      ring

private theorem sum_by_bool {A : Type*} [Fintype A] (b : A → Bool) (p : A → ℝ) :
    (∑ x, if b x = false then p x else 0) + (∑ x, if b x = true then p x else 0) =
      ∑ x, p x := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => by cases b x <;> simp

/-- Case 1 of Appendix D.1. The four child comparisons and the root comparison
yield the expected gain for a left action above the deepest internal level. -/
theorem internal_left_coin_sum_policy {h M U N T : ℕ} (e : Fin N ≃ TreeAction h M U)
    (v : TreeNode h) (hv : (v.1 : ℕ) + 1 < h)
    (pick : (t : ℕ) → FeedbackHistory t → TreeAction h M U)
    (active : ℕ → Fin (2 ^ h)) (ha : Monotone active) (η : ℝ) (leafCoin : ℕ → Bool)
    (selected : Fin (2 ^ h) → Fin M) (z : ℕ → Icc (0 : ℝ) 1)
    (draw : ℕ → TreeAction h M U → Ico (0 : ℝ) 1) :
    let i := e.symm (.inl (v, false))
    let q (c : TreeNode h → Bool) := treePlayProbability e pick active η c leafCoin selected z draw
    let u (c : TreeNode h → Bool) (t : ℕ) (j : Fin N) :=
      treeBonusProb (active t) c (leafCoin t) (selected (active t)) (e j)
    (∑ c, ∑ t ∈ Finset.range T, q c t i) / (184 * treeHeight h ^ 5) ≤
      ∑ c, bestSwapGain T (q c) (u c) i := by
  classical
  intro i q u
  let hnode : (v.1 : ℕ) < h := by omega
  let l := v.child hnode false
  let r := v.child hnode true
  have hl : (l.1 : ℕ) < h := hv
  have hr : (r.1 : ℕ) < h := hv
  have hne : l ≠ v := by
    intro he
    have hd := congrArg (fun w : TreeNode h => (w.1 : ℕ)) he
    change (v.1 : ℕ) + 1 = (v.1 : ℕ) at hd
    omega
  let p (c : TreeNode h → Bool) (t : ℕ) := q c t i
  let Q (w : TreeNode h) (c : TreeNode h → Bool) := visitMass (T := T) active (p c) w
  let LL := Q (l.child hl false)
  let LR := Q (l.child hl true)
  let RL := Q (r.child hr false)
  let RR := Q (r.child hr true)
  let G (c : TreeNode h → Bool) := bestSwapGain T (q c) (u c) i
  let H := treeHeight h
  have hH : 1 ≤ H := by dsimp [H, treeHeight]; linarith only [Nat.cast_nonneg (α := ℝ) h]
  let a := 1 / (2 * H)
  let x₁ := ∑ c, LL c
  let x₂ := ∑ c, if c l = false then LR c else 0
  let x₃ := ∑ c, if c l = true then LR c else 0
  let x₄ := ∑ c, RL c
  let x₅ := ∑ c, if c r = false then RR c else 0
  let x₆ := ∑ c, if c r = true then RR c else 0
  have hq (c : TreeNode h → Bool) (t : ℕ) (_ : t < T) (j : Fin N) : 0 ≤ q c t j :=
    (treePlayProbability_isProbVec e pick active η c leafCoin selected z draw t).1 j
  have hn (w : TreeNode h) (c : TreeNode h → Bool) : 0 ≤ Q w c :=
    visitMass_nonneg active (p c) (fun t ht => hq c t ht i) w
  have hg (c : TreeNode h → Bool) : 0 ≤ G c := bestSwapGain_nonneg (q c) (u c) i
  have h_split (w : TreeNode h) (hw : (w.1 : ℕ) < h) (c : TreeNode h → Bool) :
      Q w c = Q (w.child hw false) c + Q (w.child hw true) c :=
    visitMass_split active (p c) w hw
  have hsplit_l (c : TreeNode h → Bool) : Q l c = LL c + LR c := h_split l hl c
  have hsplit_r (c : TreeNode h → Bool) : Q r c = RL c + RR c := h_split r hr c
  have hsum_l : (∑ c, Q l c) = x₁ + x₂ + x₃ := by
    rw [Finset.sum_congr rfl (fun c _ => hsplit_l c), Finset.sum_add_distrib]
    change x₁ + (∑ c, LR c) = x₁ + x₂ + x₃
    rw [← sum_by_bool (fun c : TreeNode h → Bool => c l) LR]
    change x₁ + (x₂ + x₃) = x₁ + x₂ + x₃
    ring
  have hsum_r : (∑ c, Q r c) = x₄ + x₅ + x₆ := by
    rw [Finset.sum_congr rfl (fun c _ => hsplit_r c), Finset.sum_add_distrib]
    change x₄ + (∑ c, RR c) = x₄ + x₅ + x₆
    rw [← sum_by_bool (fun c : TreeNode h → Bool => c r) RR]
    change x₄ + (x₅ + x₆) = x₄ + x₅ + x₆
    ring
  have h_indep (w w' : TreeNode h) (ht : w.last ≤ w'.mid) (c : TreeNode h → Bool) (b : Bool) :
      Q w (Function.update c w' b) = Q w c :=
    treePlayProbability_subtree_independent e pick active ha w w' ht η c leafCoin selected z draw i b
  have hl_end : l.last = v.mid := (child_timing v hnode).1
  have hr_mid : v.mid ≤ r.mid := (child_timing v hnode).2.2.2.2
  have hLL_end : (l.child hl false).last = l.mid := (child_timing l hl).1
  have hLR_end : (l.child hl true).last = l.last := (child_timing l hl).2.2.1
  have hRL_end : (r.child hr false).last = r.mid := (child_timing r hr).1
  have hl_mid : l.mid ≤ v.mid := (child_timing v hnode).2.2.2.1
  have hLL_v := h_indep (l.child hl false) v (hLL_end.trans_le hl_mid)
  have hLL_l := h_indep (l.child hl false) l hLL_end.le
  have hLR_v := h_indep (l.child hl true) v (hLR_end.trans_le hl_end.le)
  have hL_r := h_indep l r (hl_end.trans_le hr_mid)
  have hRL_r := h_indep (r.child hr false) r hRL_end.le
  have hLL_true : (∑ c : TreeNode h → Bool, if c v = true then LL c else 0) = x₁ / 2 :=
    sum_on_fair_coin v true LL hLL_v
  have hLL_true_false :
      (∑ c : TreeNode h → Bool, if c v = true ∧ c l = false then LL c else 0) = x₁ / 4 := by
    rw [sum_on_two_coins v l hne true false LL hLL_v, sum_on_fair_coin l false LL hLL_l]
    change (x₁ / 2) / 2 = x₁ / 4
    ring
  have hLR_true_false :
      (∑ c : TreeNode h → Bool, if c v = true ∧ c l = false then LR c else 0) = x₂ / 2 :=
    sum_on_two_coins v l hne true false LR hLR_v
  have hLR_true_true :
      (∑ c : TreeNode h → Bool, if c v = true ∧ c l = true then LR c else 0) = x₃ / 2 :=
    sum_on_two_coins v l hne true true LR hLR_v
  have hRL_false : (∑ c : TreeNode h → Bool, if c r = false then RL c else 0) = x₄ / 2 :=
    sum_on_fair_coin r false RL hRL_r
  have hL_false : (∑ c : TreeNode h → Bool, if c r = false then Q l c else 0) =
      (x₁ + x₂ + x₃) / 2 := by
    rw [sum_on_fair_coin r false (Q l) hL_r, hsum_l]
  have h₁ : x₁ / (8 * H) + x₂ / (4 * H) ≤ ∑ c, G c := by
    have hc (c : TreeNode h → Bool) :
        ((if c v = true ∧ c l = false then LL c else 0) +
          (if c v = true ∧ c l = false then LR c else 0)) * a ≤ G c := by
      by_cases hcoin : c v = true ∧ c l = false
      · have hb := (internal_left_child_comparisons e v hv active c leafCoin selected (q c) (hq c)
          hcoin.1).1 hcoin.2
        change (∑ t ∈ Finset.range T, p c t * (if l.active (active t) then a else 0)) ≤ G c at hb
        rw [visitMass_weight] at hb
        change Q l c * a ≤ G c at hb
        rwa [if_pos hcoin, if_pos hcoin, ← hsplit_l]
      · simpa only [hcoin, if_false, add_zero, zero_mul] using hg c
    have hs := Finset.sum_le_sum (s := Finset.univ) fun c _ => hc c
    rw [← Finset.sum_mul, Finset.sum_add_distrib, hLL_true_false, hLR_true_false] at hs
    have he : (x₁ / 4 + x₂ / 2) * a = x₁ / (8 * H) + x₂ / (4 * H) := by
      dsimp only [a]
      ring
    exact he ▸ hs
  have h₂ : x₃ / (4 * H) - (x₁ + x₂) / 4 ≤ ∑ c, G c := by
    have hc (c : TreeNode h → Bool) :
        (if c v = true ∧ c l = true then LR c else 0) * a -
          ((if c v = true then LL c else 0) +
            (if c v = true ∧ c l = false then LR c else 0)) / 2 ≤ G c := by
      by_cases hcoin : c v = true
      · have hb := (internal_left_child_comparisons e v hv active c leafCoin selected (q c) (hq c)
          hcoin).2
        change (∑ t ∈ Finset.range T, p c t *
          (if l.active (active t) ∧ l.mid ≤ (active t : ℕ) ∧ c l = true then a
           else if l.active (active t) then -(1 / 2) else 0)) ≤ G c at hb
        rw [visitMass_child_switch active (p c) l hl] at hb
        simpa only [hcoin, true_and, if_true, add_comm, LL, LR, Q] using hb
      · by_cases hc : c l = true
        · simpa [hcoin, hc] using hg c
        · simpa [hcoin, hc] using hg c
    have hs := Finset.sum_le_sum (s := Finset.univ) fun c _ => hc c
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_div, Finset.sum_add_distrib,
      hLR_true_true, hLL_true, hLR_true_false] at hs
    have he : (x₃ / 2) * a - (x₁ / 2 + x₂ / 2) / 2 = x₃ / (4 * H) - (x₁ + x₂) / 4 := by
      dsimp only [a]
      ring
    exact he ▸ hs
  have h₃ : x₅ / (2 * H) + x₄ / (4 * H) - (x₁ + x₂ + x₃) / 4 ≤ ∑ c, G c := by
    have hc (c : TreeNode h → Bool) :
        ((if c r = false then RL c else 0) + (if c r = false then RR c else 0)) * a -
          (if c r = false then Q l c else 0) / 2 ≤ G c := by
      by_cases hcoin : c r = false
      · have hb := internal_right_child_first e v hv false active c leafCoin selected (q c) (hq c) hcoin
        simp only [and_true] at hb
        change (∑ t ∈ Finset.range T, p c t *
          (if r.active (active t) then a else if v.active (active t) then -(1 / 2) else 0)) ≤ G c at hb
        rw [visitMass_compare_right] at hb
        change Q r c * a - Q l c / 2 ≤ G c at hb
        simpa only [hcoin, if_true, ← hsplit_r] using hb
      · simpa [hcoin] using hg c
    have hs := Finset.sum_le_sum (s := Finset.univ) fun c _ => hc c
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_div, Finset.sum_add_distrib,
      hRL_false, hL_false] at hs
    change (x₄ / 2 + x₅) * a - ((x₁ + x₂ + x₃) / 2) / 2 ≤ ∑ c, G c at hs
    have he : (x₄ / 2 + x₅) * a - ((x₁ + x₂ + x₃) / 2) / 2 =
        x₅ / (2 * H) + x₄ / (4 * H) - (x₁ + x₂ + x₃) / 4 := by
      dsimp only [a]
      ring
    exact he ▸ hs
  have h₄ : x₆ / (2 * H) - (x₅ + x₄ + x₁ + x₂ + x₃) / 2 ≤ ∑ c, G c := by
    have hc (c : TreeNode h → Bool) :
        (if c r = true then RR c else 0) * a -
          ((if c r = false then RR c else 0) + RL c + Q l c) / 2 ≤ G c := by
      have hb := internal_right_child_second e v hv false active c leafCoin selected (q c) (hq c)
      simp only [and_true] at hb
      change (∑ t ∈ Finset.range T, p c t *
        (if r.active (active t) ∧ r.mid ≤ (active t : ℕ) ∧ c r = true then a
         else if r.active (active t) ∨ v.active (active t) then -(1 / 2) else 0)) ≤ G c at hb
      rw [visitMass_compare_right_switch active (p c) v hnode r rfl hr] at hb
      exact hb
    have hs := Finset.sum_le_sum (s := Finset.univ) fun c _ => hc c
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_div, Finset.sum_add_distrib,
      Finset.sum_add_distrib, hsum_l] at hs
    change x₆ * a - (x₅ + x₄ + (x₁ + x₂ + x₃)) / 2 ≤ ∑ c, G c at hs
    have he : x₆ * a - (x₅ + x₄ + (x₁ + x₂ + x₃)) / 2 =
        x₆ / (2 * H) - (x₅ + x₄ + x₁ + x₂ + x₃) / 2 := by
      dsimp only [a]
      ring
    exact he ▸ hs
  have h₅ : (∑ c, ∑ t ∈ Finset.range T, p c t) / (4 * H) -
      (x₁ + x₂ + x₃ + x₄ + x₅ + x₆) / 2 ≤ ∑ c, G c := by
    have hc (c : TreeNode h → Bool) : (∑ t ∈ Finset.range T, p c t) / (4 * H) -
        (Q l c + Q r c) / 2 ≤ G c := by
      rw [← h_split v hnode c]
      exact internal_root_support_gain e v hnode false active c leafCoin selected (q c) (hq c)
    have hs := Finset.sum_le_sum (s := Finset.univ) fun c _ => hc c
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div, Finset.sum_add_distrib,
      hsum_l, hsum_r] at hs
    have he : x₁ + x₂ + x₃ + (x₄ + x₅ + x₆) = x₁ + x₂ + x₃ + x₄ + x₅ + x₆ := by ring
    rwa [he] at hs
  have hx₁ : 0 ≤ x₁ := Finset.sum_nonneg fun c _ => hn _ c
  have hx₂ : 0 ≤ x₂ := Finset.sum_nonneg fun c _ => by split; exact hn _ c; exact le_rfl
  have hx₃ : 0 ≤ x₃ := Finset.sum_nonneg fun c _ => by split; exact hn _ c; exact le_rfl
  have hx₄ : 0 ≤ x₄ := Finset.sum_nonneg fun c _ => hn _ c
  have hx₅ : 0 ≤ x₅ := Finset.sum_nonneg fun c _ => by split; exact hn _ c; exact le_rfl
  exact internal_left_gain_of_comparisons hH (Finset.sum_nonneg fun c _ => hg c)
    hx₁ hx₂ hx₃ hx₄ hx₅ h₁ h₂ h₃ h₄ h₅

/-- The embedded auxiliary actions of the tree. -/
def treeAuxAction {h M U N : ℕ} (e : Fin N ≃ TreeAction h M U) : Fin M ↪ Fin N where
  toFun j := e.symm (.inr (.inl j))
  inj' := by
    intro j k hj
    have he := e.symm.injective hj
    simpa only [Sum.inr.injEq, Sum.inl.injEq] using he

/-- For each nonauxiliary action the coin average accounts for its share of
the time horizon. This holds for a fixed reward tape and auxiliary table. -/
theorem tree_nonaux_coin_sum {h M U N T : ℕ} (hh : 0 < h)
    (e : Fin N ≃ TreeAction h M U)
    (pick : (t : ℕ) → FeedbackHistory t → TreeAction h M U)
    (active : ℕ → Fin (2 ^ h)) (ha : Monotone active) (η : ℝ)
    (selected : Fin (2 ^ h) → Fin M) (z : ℕ → Icc (0 : ℝ) 1)
    (draw : ℕ → TreeAction h M U → Ico (0 : ℝ) 1)
    (i : Fin N) (hi : ∀ j, treeAuxAction e j ≠ i) :
    let leafCoin (b : Fin T → Bool) (t : ℕ) := if ht : t < T then b ⟨t, ht⟩ else false
    let q (b : Fin T → Bool) (c : TreeNode h → Bool) :=
      treePlayProbability e pick active η c (leafCoin b) selected z draw
    let u (b : Fin T → Bool) (c : TreeNode h → Bool) (t : ℕ) (j : Fin N) :=
      treeBonusProb (active t) c (leafCoin b t) (selected (active t)) (e j)
    (∑ b, ∑ c, ∑ t ∈ Finset.range T, q b c t i) / (184 * treeHeight h ^ 5) ≤
      ∑ b, ∑ c, bestSwapGain T (q b c) (u b c) i := by
  classical
  intro leafCoin q u
  let H := treeHeight h
  have hH : 1 ≤ H := by dsimp [H, treeHeight]; linarith only [Nat.cast_nonneg (α := ℝ) h]
  have hH' : 0 < H := zero_lt_one.trans_le hH
  have hhpow : H ≤ H ^ 5 := by simpa only [pow_one] using pow_le_pow_right₀ hH (show 1 ≤ 5 by decide)
  have hq (b : Fin T → Bool) (c : TreeNode h → Bool) (t : ℕ) (j : Fin N) : 0 ≤ q b c t j :=
    (treePlayProbability_isProbVec e pick active η c (leafCoin b) selected z draw t).1 j
  have he : i = e.symm (e i) := (e.symm_apply_apply i).symm
  rcases hcase : e i with ⟨v, side⟩ | (j | j)
  · rw [hcase] at he
    rcases eq_or_lt_of_le (Nat.le_of_lt_succ v.1.isLt) with hv | hv
    · rw [Finset.sum_comm (f := fun b c => ∑ t ∈ Finset.range T, q b c t i),
        Finset.sum_comm (f := fun b c => bestSwapGain T (q b c) (u b c) i), Finset.sum_div]
      refine Finset.sum_le_sum fun c _ => ?_
      have hleaf := leaf_coin_sum_policy (T := T) hh e v hv side pick active η c selected z draw
      rw [he]
      refine le_trans ?_ hleaf
      exact div_le_div_of_nonneg_left
        (Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun t _ => hq b c t _)
        (by positivity : 0 < 8 * H) (by linarith)
    · rw [Finset.sum_div]
      refine Finset.sum_le_sum fun b _ => ?_
      rcases lt_or_eq_of_le (Nat.succ_le_of_lt hv) with hv' | hv'
      · cases side
        · rw [he]
          exact internal_left_coin_sum_policy (T := T) e v hv' pick active ha η (leafCoin b) selected z draw
        · rw [he]
          exact internal_right_coin_sum_policy (T := T) e v hv' pick active ha η (leafCoin b) selected z draw
      · cases side
        · rw [he]
          exact deepest_left_coin_sum_policy (T := T) e v hv' pick active ha η (leafCoin b) selected z draw
        · rw [Finset.sum_div]
          refine Finset.sum_le_sum fun c _ => ?_
          rw [he]
          exact deepest_right_bestSwapGain e v hv' active c (leafCoin b) selected (q b c)
            (fun t _ j' => hq b c t j')
  · exact (hi j (by rw [he, hcase]; rfl)).elim
  · rw [hcase] at he
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun b _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun c _ => ?_
    let rootA := e.symm (.inl (TreeNode.root h, false))
    let rootB := e.symm (.inl (TreeNode.root h, true))
    have hroot (t : ℕ) (_ : t < T) : u b c t rootA + u b c t rootB = 1 / (2 * H) := by
      simp only [u, rootA, rootB, Equiv.apply_symm_apply]
      exact treeBonusProb_root_pair hh (active t) c (leafCoin b t) (selected (active t))
    have hzero (t : ℕ) (_ : t < T) : u b c t i = 0 := by simp [u, hcase, treeBonusProb]
    refine le_trans ?_ (unnamed_bestSwapGain (q b c) (u b c) i rootA rootB H hzero hroot)
    exact div_le_div_of_nonneg_left (Finset.sum_nonneg fun t _ => hq b c t i)
      (by positivity : 0 < 4 * H) (by linarith)

/-- Comparing all auxiliary actions with the root pair leaves just the
count of plays of the selected auxiliary action as the loss term. -/
theorem tree_auxiliary_gain {h M U N T : ℕ} (hh : 0 < h) (e : Fin N ≃ TreeAction h M U)
    (active : ℕ → Fin (2 ^ h)) (c : TreeNode h → Bool) (leafCoin : ℕ → Bool)
    (selected : Fin (2 ^ h) → Fin M) (q : ℕ → Fin N → ℝ) :
    let u (t : ℕ) (i : Fin N) := treeBonusProb (active t) c (leafCoin t) (selected (active t)) (e i)
    let aux := treeAuxAction e
    ((∑ j : Fin M, ∑ t ∈ Finset.range T, q t (aux j)) / (4 * treeHeight h) -
        ∑ t ∈ Finset.range T, q t (aux (selected (active t)))) ≤
      ∑ j : Fin M, bestSwapGain T q u (aux j) := by
  classical
  intro u aux
  let rootA := e.symm (.inl (TreeNode.root h, false))
  let rootB := e.symm (.inl (TreeNode.root h, true))
  have hroot (t : ℕ) (_ : t < T) : u t rootA + u t rootB = 1 / (2 * treeHeight h) := by
    simp only [u, rootA, rootB, Equiv.apply_symm_apply]
    exact treeBonusProb_root_pair hh (active t) c (leafCoin t) (selected (active t))
  have hc (j : Fin M) := root_bestSwapGain q u (aux j) rootA rootB (treeHeight h) hroot
  have hs := Finset.sum_le_sum (s := Finset.univ) fun j _ => hc j
  rw [Finset.sum_sub_distrib, ← Finset.sum_div] at hs
  have he : (∑ j : Fin M, ∑ t ∈ Finset.range T, q t (aux j) * u t (aux j)) =
      ∑ t ∈ Finset.range T, q t (aux (selected (active t))) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    have hu (j : Fin M) : u t (aux j) = if j = selected (active t) then 1 else 0 := by
      change treeBonusProb (U := U) (active t) c (leafCoin t) (selected (active t))
        (e (e.symm (.inr (.inl j)))) = _
      rw [Equiv.apply_symm_apply]
      rfl
    simp only [hu, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rwa [he] at hs

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open MeasureTheory Set
open scoped ENNReal

theorem monotone_blockLeaf (h r : ℕ) : Monotone (blockLeaf h r) := by
  intro s t hst
  exact min_le_min_right _ (Nat.div_le_div_right hst)

theorem blockLeaf_within {h r : ℕ} (l : Fin (2 ^ h)) {t : ℕ} (ht : t < r) :
    blockLeaf h r (l.val * r + t) = l := by
  apply Fin.ext
  change min ((l.val * r + t) / r) (2 ^ h - 1) = l.val
  have hr : 0 < r := Nat.zero_lt_of_lt ht
  rw [Nat.mul_comm l.val r, Nat.mul_add_div hr, Nat.div_eq_of_lt ht, add_zero, min_eq_left]
  omega

theorem blockLeaf_before {h r : ℕ} (l : Fin (2 ^ h)) {t : ℕ} (ht : t < l.val * r) :
    blockLeaf h r t ≠ l := by
  have hr : 0 < r := by
    by_contra! hn
    simp [Nat.eq_zero_of_le_zero hn] at ht
  have hdiv := (Nat.div_lt_iff_lt_mul hr).mpr ht
  intro he
  have he' := congrArg Fin.val he
  change min (t / r) (2 ^ h - 1) = l.val at he'
  exact hdiv.not_ge (he'.symm.trans_le (min_le_left _ _))

/-- Sum over all rounds by summing over the equal-length periods. -/
theorem sum_blocks {A : Type*} [AddCommMonoid A] (f : ℕ → A) (l r : ℕ) :
    (∑ j : Fin l, ∑ t : Fin r, f (j.val * r + t.val)) = ∑ t ∈ Finset.range (l * r), f t := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [Fin.sum_univ_castSucc, Nat.succ_mul, Finset.sum_range_add]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih, Fin.sum_univ_eq_sum_range (fun t : ℕ => f (l * r + t))]

theorem integral_finiteTableLaw {A : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (f : A → ℝ) :
    (∫ a, f a ∂finiteTableLaw A) = (∑ a, f a) / Fintype.card A := by
  rw [finiteTableLaw, integral_smul_measure, integral_count, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, smul_eq_mul, div_eq_inv_mul]

/-- A uniform table can be averaged by fixing it and averaging over a fresh
value at one coordinate. Swap the old value and the fresh value to see this. -/
theorem sum_update_average {A B : Type*} [Fintype A] [Fintype B] [Nonempty B]
    [DecidableEq A] (a : A) (f : (A → B) → ℝ) :
    (∑ g : A → B, (∑ b : B, f (Function.update g a b)) / Fintype.card B) = ∑ g, f g := by
  classical
  let flip (p : (A → B) × B) := (Function.update p.1 a p.2, p.1 a)
  have hflip : Function.Involutive flip := by
    intro p
    apply Prod.ext
    · funext a'
      by_cases ha : a' = a
      · subst a'
        simp [flip]
      · simp [flip, Function.update_of_ne ha]
    · simp [flip]
  let e : ((A → B) × B) ≃ ((A → B) × B) := ⟨flip, flip, hflip, hflip⟩
  have he := e.sum_comp (fun p => f p.1)
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at he
  change (∑ g : A → B, ∑ b : B, f (Function.update g a b)) = ∑ g : A → B, ∑ _ : B, f g at he
  rw [← Finset.sum_div, he]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
  have hb : (Fintype.card B : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open MeasureTheory Set

theorem measurable_tapeDraw {N T : ℕ} (t : ℕ) : Measurable (fun tape : RewardTape N T => tapeDraw tape t) := by
  by_cases ht : t < T
  · simp only [tapeDraw, dif_pos ht]
    exact measurable_snd.comp (measurable_rewardTapePrefix N (Nat.succ_le_of_lt ht))
  · simp only [tapeDraw, dif_neg ht]
    exact measurable_const

noncomputable def treeEnvironmentPlay {h M U N T : ℕ} (e : Fin N ≃ TreeAction h M U)
    (active : ℕ → Fin (2 ^ h)) (η : ℝ) (pick : (t : ℕ) → FeedbackHistory t → Fin N)
    (anchor : Fin N) (env : TreeEnvironment h M N T) (t : ℕ) : Fin N → ℝ :=
  Pi.single (treeEnvironmentAction e active η pick anchor env t) 1

theorem measurable_with_fixed_table {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [Fintype A] [MeasurableSingletonClass A] {f : A × B → C}
    (hf : ∀ a, Measurable (fun b => f (a, b))) : Measurable f := by
  intro S hS
  have he : f ⁻¹' S = ⋃ a, {a} ×ˢ ((fun b => f (a, b)) ⁻¹' S) := by
    ext ⟨a, b⟩
    simp
  rw [he]
  exact MeasurableSet.iUnion fun a => (measurableSet_singleton a).prod (hf a hS)

theorem measurable_treeEnvironmentReward {h M U N T : ℕ} (e : Fin N ≃ TreeAction h M U)
    (active : ℕ → Fin (2 ^ h)) (η : ℝ) (t : ℕ) (i : Fin N) :
    Measurable (fun env : TreeEnvironment h M N T => treeEnvironmentReward e active η env t i) := by
  apply measurable_with_fixed_table
  intro table
  exact (measurable_boundedRoundReward η (tableBonuses e active table t i) i).comp (measurable_tapeDraw t)

theorem measurable_treeEnvironmentAction {h M U N T : ℕ} (e : Fin N ≃ TreeAction h M U)
    (active : ℕ → Fin (2 ^ h)) (η : ℝ) (pick : (t : ℕ) → FeedbackHistory t → Fin N)
    (hm : ∀ t, Measurable (pick t)) (anchor : Fin N) (t : ℕ) :
    Measurable (fun env : TreeEnvironment h M N T => treeEnvironmentAction e active η pick anchor env t) := by
  apply measurable_with_fixed_table
  intro table
  by_cases ht : t < T
  · simp only [treeEnvironmentAction, dif_pos ht]
    exact (hm t).comp ((measurable_rawTapeHistory η (tableBonuses e active table) pick hm t).comp
      (measurable_rewardTapePrefix N ht.le))
  · simp only [treeEnvironmentAction, dif_neg ht]
    exact measurable_const

theorem measurable_treeEnvironmentPlay {h M U N T : ℕ} (e : Fin N ≃ TreeAction h M U)
    (active : ℕ → Fin (2 ^ h)) (η : ℝ) (pick : (t : ℕ) → FeedbackHistory t → Fin N)
    (hm : ∀ t, Measurable (pick t)) (anchor : Fin N) (t : ℕ) (i : Fin N) :
    Measurable (fun env : TreeEnvironment h M N T => treeEnvironmentPlay e active η pick anchor env t i) :=
  (Measurable.of_discrete (f := fun a : Fin N => (Pi.single a (1 : ℝ) : Fin N → ℝ) i)).comp
    (measurable_treeEnvironmentAction e active η pick hm anchor t)

theorem treeEnvironmentPlay_probVec {h M U N T : ℕ} (e : Fin N ≃ TreeAction h M U)
    (active : ℕ → Fin (2 ^ h)) (η : ℝ) (pick : (t : ℕ) → FeedbackHistory t → Fin N)
    (anchor : Fin N) (env : TreeEnvironment h M N T) (t : ℕ) :
    IsProbVec (treeEnvironmentPlay e active η pick anchor env t) := by
  unfold treeEnvironmentPlay
  constructor
  · intro i
    rw [Pi.single_apply]
    split <;> norm_num
  · simp

theorem rawTapeHistory_eq_feedbackHistory {N T : ℕ} (η : ℝ) (u : ℕ → Fin N → ℝ)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (tape : RewardTape N T) (t : ℕ) (ht : t ≤ T) :
    rawTapeHistory η u pick t (rewardTapePrefix N ht tape) =
      feedbackHistory pick (fun s i => boundedRoundReward η (u s i) i (tapeDraw tape s)) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have he : (rewardTapePrefix N ht tape).1 = rewardTapePrefix N ((Nat.le_succ t).trans ht) tape := by
      have hf : rewardTapePrefix N (Nat.le_succ t) = (Prod.fst : RewardTape N (t + 1) → RewardTape N t) := by
        rw [rewardTapePrefix_succ N (le_refl t), rewardTapePrefix_refl, Function.id_comp]
      have hc := congrFun (rewardTapePrefix_comp N (Nat.le_succ t) ht) tape
      rw [hf] at hc
      exact hc
    have hdraw : tapeDraw tape t = (rewardTapePrefix N ht tape).2 := by
      simp only [tapeDraw, dif_pos (Nat.lt_of_succ_le ht)]
    have hhist := ih ((Nat.le_succ t).trans ht)
    simp only [rawTapeHistory, feedbackHistory, he, hhist, hdraw]
    rfl

private theorem feedbackHistory_map_actions {A B : Type*} (f : A → B)
    (pick : (t : ℕ) → FeedbackHistory t → A) (y : ℕ → B → ℝ) (t : ℕ) :
    feedbackHistory (fun s x => f (pick s x)) y t =
      feedbackHistory pick (fun s a => y s (f a)) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [feedbackHistory, ih]
    rfl

/-- Relate the measurable tape model to the action probabilities used in
the deterministic tree comparison lemmas. -/
theorem treeEnvironmentPlay_eq_treePlayProbability {h M U N T : ℕ} (e : Fin N ≃ TreeAction h M U)
    (active : ℕ → Fin (2 ^ h)) (η : ℝ) (pick : (t : ℕ) → FeedbackHistory t → Fin N)
    (anchor : Fin N) (env : TreeEnvironment h M N T) (t : ℕ) (ht : t < T) (i : Fin N) :
    treeEnvironmentPlay e active η pick anchor env t i =
      treePlayProbability e (fun s p => e (pick s p)) active η env.1.2.1
        (tableLeafCoin env.1.1) env.1.2.2
        (fun s => supportedBase (tapeDraw env.2 s).1)
        (fun s a => supportedThreshold ((tapeDraw env.2 s).2 (e.symm a))) t i := by
  classical
  unfold treeEnvironmentPlay treeEnvironmentAction treePlayProbability
  simp only [dif_pos ht, Pi.single_apply]
  have hy (s : ℕ) (a : TreeAction h M U) :
      treeReward η (active s) env.1.2.1 (tableLeafCoin env.1.1 s)
          (env.1.2.2 (active s)) (supportedBase (tapeDraw env.2 s).1)
          (fun a' => supportedThreshold ((tapeDraw env.2 s).2 (e.symm a'))) a =
        treeEnvironmentReward e active η env s (e.symm a) := by
    simp only [treeEnvironmentReward, boundedRoundReward, tableBonuses, scheduledBonuses,
      Equiv.apply_symm_apply, treeReward]
  have hy' : (fun s a => treeReward η (active s) env.1.2.1 (tableLeafCoin env.1.1 s)
      (env.1.2.2 (active s)) (supportedBase (tapeDraw env.2 s).1)
      (fun a' => supportedThreshold ((tapeDraw env.2 s).2 (e.symm a'))) a) =
      (fun s a => treeEnvironmentReward e active η env s (e.symm a)) := funext fun s => funext (hy s)
  rw [hy', feedbackHistory_map_actions]
  simp only [Equiv.symm_apply_apply]
  rw [rawTapeHistory_eq_feedbackHistory η (tableBonuses e active env.1) pick env.2 t ht.le]
  have hiff : (i = pick t (feedbackHistory pick (treeEnvironmentReward e active η env) t)) ↔
      e (pick t (feedbackHistory pick (treeEnvironmentReward e active η env) t)) = e i := by
    rw [Equiv.apply_eq_iff_eq]
    exact eq_comm
  let a := pick t (feedbackHistory pick (treeEnvironmentReward e active η env) t)
  change (if i = a then (1 : ℝ) else 0) = if e a = e i then 1 else 0
  by_cases hi : i = a
  · rw [if_pos hi, if_pos (hiff.mp hi)]
  · rw [if_neg hi, if_neg (fun he => hi (hiff.mpr he))]

theorem integrable_treeEnvironmentBestGain {h M U N T : ℕ} [Nonempty (Fin M)]
    (e : Fin N ≃ TreeAction h M U) (active : ℕ → Fin (2 ^ h)) (η : ℝ)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (hm : ∀ t, Measurable (pick t))
    (anchor i : Fin N) :
    Integrable (fun env : TreeEnvironment h M N T =>
      bestSwapGain T (treeEnvironmentPlay e active η pick anchor env) (tableBonuses e active env.1) i)
      (treeEnvironmentLaw h M N T) := by
  classical
  let q := treeEnvironmentPlay (T := T) e active η pick anchor
  let u (env : TreeEnvironment h M N T) := tableBonuses e active env.1
  have hu (env : TreeEnvironment h M N T) (t : ℕ) (j : Fin N) : u env t j ∈ Icc 0 1 :=
    treeBonusProb_mem _ _ _ _ _
  have hqm (t : ℕ) (k : Fin N) : Measurable (fun env => q env t k) :=
    measurable_treeEnvironmentPlay e active η pick hm anchor t k
  have hum (t : ℕ) (j : Fin N) : Measurable (fun env => u env t j) := by
    apply measurable_with_fixed_table
    intro table
    change Measurable (fun _ : RewardTape N T => tableBonuses e active table t j)
    exact measurable_const
  let _ : Nonempty (Fin N) := ⟨anchor⟩
  unfold bestSwapGain
  apply integrable_finset_max (B := (T : ℝ))
  · intro j
    exact Finset.measurable_sum _ fun t _ => (hqm t i).mul ((hum t j).sub (hum t i))
  · intro j env
    unfold swapGain
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      _ ≤ ∑ _ ∈ Finset.range T, (1 : ℝ) := Finset.sum_le_sum fun t _ => by
        have hd : |u env t j - u env t i| ≤ 1 := abs_le.mpr
          ⟨by linarith only [(hu env t j).1, (hu env t i).2],
            by linarith only [(hu env t j).2, (hu env t i).1]⟩
        have hq : |q env t i| ≤ 1 := by
          unfold q treeEnvironmentPlay
          rw [Pi.single_apply]
          split <;> norm_num
        rw [abs_mul]
        exact mul_le_one₀ hq (abs_nonneg _) hd
      _ = _ := by simp

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open MeasureTheory Set

private theorem treeTableSum {h M T : ℕ} (f : TreeTables h M T → ℝ) :
    (∑ table, f table) = ∑ b : Fin T → Bool, ∑ c : TreeNode h → Bool,
      ∑ J : Fin (2 ^ h) → Fin M, f (b, c, J) := by
  simp only [Fintype.sum_prod_type]

private theorem sum_treeTableSum_selected_first {h M T : ℕ} (f : TreeTables h M T → ℝ) :
    (∑ table, f table) = ∑ J : Fin (2 ^ h) → Fin M, ∑ b : Fin T → Bool,
      ∑ c : TreeNode h → Bool, f (b, c, J) := by
  rw [treeTableSum]
  calc
    _ = ∑ b : Fin T → Bool, ∑ J : Fin (2 ^ h) → Fin M, ∑ c : TreeNode h → Bool, f (b, c, J) :=
      Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = _ := Finset.sum_comm

theorem integrable_treePlayMass {h M U N T : ℕ} [Nonempty (Fin M)]
    (e : Fin N ≃ TreeAction h M U) (active : ℕ → Fin (2 ^ h)) (η : ℝ)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (hm : ∀ t, Measurable (pick t))
    (anchor : Fin N) (a : TreeTables h M T → ℕ → Fin N) :
    Integrable (fun env : TreeEnvironment h M N T =>
      ∑ t ∈ Finset.range T, treeEnvironmentPlay e active η pick anchor env t (a env.1 t))
      (treeEnvironmentLaw h M N T) := by
  classical
  apply integrable_finsetSum
  intro t _
  have hq : Measurable (fun env : TreeEnvironment h M N T =>
      treeEnvironmentPlay e active η pick anchor env t (a env.1 t)) := by
    exact measurable_select ((Measurable.of_discrete (f := fun table => a table t)).comp measurable_fst)
      (fun i => measurable_treeEnvironmentPlay e active η pick hm anchor t i)
  apply Integrable.of_bound hq.aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro env
  unfold treeEnvironmentPlay
  rw [Pi.single_apply]
  split <;> norm_num

/-- Extend the fixed-tape coin bound to the full distribution. -/
theorem tree_nonaux_expected_gain {h M U N T : ℕ} [Nonempty (Fin M)] (hh : 0 < h)
    (e : Fin N ≃ TreeAction h M U) (active : ℕ → Fin (2 ^ h)) (ha : Monotone active) (η : ℝ)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (hm : ∀ t, Measurable (pick t))
    (anchor i : Fin N) (hi : ∀ j, treeAuxAction e j ≠ i) :
    let P := treeEnvironmentLaw h M N T
    let q := treeEnvironmentPlay (T := T) e active η pick anchor
    let u (env : TreeEnvironment h M N T) := tableBonuses e active env.1
    (∫ env, ∑ t ∈ Finset.range T, q env t i ∂P) / (184 * treeHeight h ^ 5) ≤
      ∫ env, bestSwapGain T (q env) (u env) i ∂P := by
  classical
  intro P q u
  let C := TreeTables h M T
  let μ := finiteTableLaw C
  let ν := rewardTapeLaw N T
  let Q (env : C × RewardTape N T) := ∑ t ∈ Finset.range T, q env t i
  let G (env : C × RewardTape N T) := bestSwapGain T (q env) (u env) i
  have hQ : Integrable Q (μ.prod ν) := integrable_treePlayMass e active η pick hm anchor (fun _ _ => i)
  have hG : Integrable G (μ.prod ν) := integrable_treeEnvironmentBestGain e active η pick hm anchor i
  let D := 184 * treeHeight h ^ 5
  have hfixed (tape : RewardTape N T) : (∫ table, Q (table, tape) ∂μ) / D ≤
      ∫ table, G (table, tape) ∂μ := by
    rw [integral_finiteTableLaw, integral_finiteTableLaw]
    rw [show ((∑ table : C, Q (table, tape)) / Fintype.card C) / D =
        ((∑ table : C, Q (table, tape)) / D) / Fintype.card C from by ring]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    rw [sum_treeTableSum_selected_first, sum_treeTableSum_selected_first, Finset.sum_div]
    refine Finset.sum_le_sum fun J _ => ?_
    let z (s : ℕ) := supportedBase (tapeDraw tape s).1
    let draw (s : ℕ) (a : TreeAction h M U) := supportedThreshold ((tapeDraw tape s).2 (e.symm a))
    let q' (b : Fin T → Bool) (c : TreeNode h → Bool) :=
      treePlayProbability e (fun s p => e (pick s p)) active η c (tableLeafCoin b) J z draw
    have hq (b : Fin T → Bool) (c : TreeNode h → Bool) (t : ℕ) (ht : t ∈ Finset.range T) (j : Fin N) :
        q ((b, c, J), tape) t j = q' b c t j :=
      treeEnvironmentPlay_eq_treePlayProbability e active η pick anchor ((b, c, J), tape) t
        (Finset.mem_range.mp ht) j
    have hmass (b : Fin T → Bool) (c : TreeNode h → Bool) :
        Q ((b, c, J), tape) = ∑ t ∈ Finset.range T, q' b c t i :=
      Finset.sum_congr rfl (fun t ht => hq b c t ht i)
    have hgain (b : Fin T → Bool) (c : TreeNode h → Bool) :
        G ((b, c, J), tape) = bestSwapGain T (q' b c) (u ((b, c, J), tape)) i := by
      unfold G bestSwapGain
      congr 1
      funext j
      unfold swapGain
      exact Finset.sum_congr rfl fun t ht => by rw [hq b c t ht i]
    simp only [hmass, hgain]
    exact tree_nonaux_coin_sum (T := T) hh e (fun s p => e (pick s p)) active ha η J z draw i hi
  change (∫ env, Q env ∂μ.prod ν) / D ≤ ∫ env, G env ∂μ.prod ν
  rw [integral_prod_symm Q hQ, integral_prod_symm G hG, ← integral_div]
  exact integral_mono (hQ.swap.integral_prod_left.div_const _) hG.swap.integral_prod_left hfixed

/-- Averaging over all tables, the learner's expected number of selected
auxiliary plays is bounded by the sum of the bounds for each period. -/
theorem tree_expected_selected_hits {h M U N r : ℕ} [Nonempty (Fin M)]
    (e : Fin N ≃ TreeAction h M U) (η : ℝ) (hη : 0 ≤ η) (hη₁ : η < 1)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (hm : ∀ t, Measurable (pick t)) (anchor : Fin N) :
    let L := 2 ^ h
    let T := L * r
    let active := blockLeaf h r
    let P := treeEnvironmentLaw h M N T
    let q := treeEnvironmentPlay (T := T) e active η pick anchor
    (∫ env, ∑ t ∈ Finset.range T, q env t (treeAuxAction e (env.1.2.2 (active t))) ∂P) ≤
      (L : ℝ) * ((r : ℝ) / M + η * r * Real.sqrt ((r : ℝ) / (6 * M))) := by
  classical
  intro L T active P q
  let C := TreeTables h M T
  let μ := finiteTableLaw C
  let ν := rewardTapeLaw N T
  let aux := treeAuxAction e
  let u (table : C) := tableBonuses e active table
  let B := (r : ℝ) / M + η * r * Real.sqrt ((r : ℝ) / (6 * M))
  let W (env : TreeEnvironment h M N T) := ∑ t ∈ Finset.range T,
    q env t (aux (env.1.2.2 (active t)))
  have hW : Integrable W (μ.prod ν) :=
    integrable_treePlayMass e active η pick hm anchor (fun table t => aux (table.2.2 (active t)))
  have he (l : Fin L) : l.val * r + r ≤ T := by
    have h := Nat.mul_le_mul_right r (Nat.succ_le_of_lt l.isLt)
    rwa [Nat.succ_mul] at h
  let f (l : Fin L) (env : TreeEnvironment h M N T) :=
    globalPeriodHits η (u env.1) pick (aux (env.1.2.2 l)) (l.val * r) r (he l) env.2
  have hf (l : Fin L) : Integrable (f l) (μ.prod ν) := by
    have hm' : Measurable (f l) := by
      apply measurable_with_fixed_table
      intro table
      exact measurable_globalPeriodHits η (u table) pick hm (aux (table.2.2 l)) (l.val * r) r (he l)
    apply Integrable.of_bound hm'.aestronglyMeasurable r
    exact Filter.Eventually.of_forall (fun env => Real.norm_eq_abs _ ▸
      abs_globalPeriodHits η (u env.1) pick (aux (env.1.2.2 l)) (l.val * r) r (he l) env.2)
  have hf_eq (env : TreeEnvironment h M N T) : W env = ∑ l : Fin L, f l env := by
    unfold W
    rw [← sum_blocks (fun t => q env t (aux (env.1.2.2 (active t)))) L r]
    refine Finset.sum_congr rfl fun l _ => ?_
    unfold f globalPeriodHits
    refine Finset.sum_congr rfl fun i _ => ?_
    have ht : l.val * r + i.val < T := (Nat.add_lt_add_left i.isLt _).trans_le (he l)
    have ha : active (l.val * r + i.val) = l := blockLeaf_within l i.isLt
    simp only [q, treeEnvironmentPlay, treeEnvironmentAction, dif_pos ht, Pi.single_apply, ha]
    by_cases hh : pick (l.val * r + i.val) (rawTapeHistory η (u env.1) pick (l.val * r + i.val)
        (rewardTapePrefix N ht.le env.2)) = aux (env.1.2.2 l)
    · simp [hh, u]
    · simp [hh, Ne.symm hh, u]
  have hper (l : Fin L) : (∫ env, f l env ∂μ.prod ν) ≤ B := by
    rw [integral_prod (f l) (hf l), integral_finiteTableLaw]
    apply (div_le_iff₀ (show 0 < (Fintype.card C : ℝ) by exact_mod_cast Fintype.card_pos)).mpr
    rw [treeTableSum]
    have hadd (b : Fin T → Bool) (c : TreeNode h → Bool) :
        (∑ J : Fin (2 ^ h) → Fin M, ∫ tape, f l ((b, c, J), tape) ∂ν) ≤
          ∑ _ : Fin (2 ^ h) → Fin M, B := by
      rw [← sum_update_average l (fun J => ∫ tape, f l ((b, c, J), tape) ∂ν)]
      refine Finset.sum_le_sum fun J _ => ?_
      have hb := tree_global_period_average e η hη hη₁ active l (l.val * r) r (he l)
        (fun _ ht => blockLeaf_before l ht) (fun _ ht => blockLeaf_within l ht)
        c (tableLeafCoin b) J pick hm
      have he' (j : Fin M) : (Function.update J l j) l = j := Function.update_self ..
      simp only [f, u, tableBonuses, aux, treeAuxAction, he'] at *
      rw [Fintype.card_fin]
      exact hb
    have hc := Finset.sum_le_sum (s := Finset.univ) fun b _ =>
      Finset.sum_le_sum (s := Finset.univ) fun c _ => hadd b c
    refine hc.trans_eq ?_
    rw [← treeTableSum (f := fun _ : C => B)]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  change ∫ env, W env ∂μ.prod ν ≤ (L : ℝ) * B
  have hw : (fun env => W env) = fun env => ∑ l, f l env := funext hf_eq
  rw [hw, integral_finsetSum _ (fun l _ => hf l)]
  exact (Finset.sum_le_sum (s := Finset.univ) (fun l _ => hper l)).trans_eq (by simp)

set_option maxHeartbeats 750000 in
/-- The whole-tree predicted gain. The two groups of source actions
partition all play mass. -/
theorem tree_expected_proxy {h M U N r : ℕ} [Nonempty (Fin M)] (hh : 0 < h)
    (e : Fin N ≃ TreeAction h M U) (η : ℝ) (hη : 0 ≤ η) (hη₁ : η < 1)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (hm : ∀ t, Measurable (pick t)) (anchor : Fin N)
    (hbudget : ((2 ^ h : ℕ) : ℝ) * ((r : ℝ) / M + η * r * Real.sqrt ((r : ℝ) / (6 * M))) ≤
      ((2 ^ h * r : ℕ) : ℝ) / (64 * treeHeight h)) :
    let T := 2 ^ h * r
    let active := blockLeaf h r
    let P := treeEnvironmentLaw h M N T
    let q := treeEnvironmentPlay (T := T) e active η pick anchor
    (T : ℝ) / (368 * treeHeight h ^ 5) ≤
      ∫ env, pseudoSwapRegret T (q env) (tableBonuses e active env.1) ∂P := by
  classical
  intro T active P q
  let H := treeHeight h
  let aux := treeAuxAction e
  let A := Finset.univ.map aux
  let u (env : TreeEnvironment h M N T) := tableBonuses e active env.1
  let Q (i : Fin N) (env : TreeEnvironment h M N T) := ∑ t ∈ Finset.range T, q env t i
  let G (i : Fin N) (env : TreeEnvironment h M N T) := bestSwapGain T (q env) (u env) i
  let W (env : TreeEnvironment h M N T) :=
    ∑ t ∈ Finset.range T, q env t (aux (env.1.2.2 (active t)))
  let meanQ (i : Fin N) := ∫ env, Q i env ∂P
  let meanG (i : Fin N) := ∫ env, G i env ∂P
  have hQ (i : Fin N) : Integrable (Q i) P :=
    integrable_treePlayMass e active η pick hm anchor (fun _ _ => i)
  have hG (i : Fin N) : Integrable (G i) P :=
    integrable_treeEnvironmentBestGain e active η pick hm anchor i
  have hW : Integrable W P :=
    integrable_treePlayMass e active η pick hm anchor (fun tb t => aux (tb.2.2 (active t)))
  have htotalQ : (∑ i, meanQ i) = T := by
    dsimp only [meanQ]
    rw [← integral_finsetSum _ (fun i _ => hQ i)]
    have he (env : TreeEnvironment h M N T) : (∑ i, Q i env) = T := by
      unfold Q
      rw [Finset.sum_comm]
      calc
        _ = ∑ _ ∈ Finset.range T, (1 : ℝ) :=
          Finset.sum_congr rfl fun t _ => (treeEnvironmentPlay_probVec e active η pick anchor env t).2
        _ = _ := by simp
    simp only [he, integral_const, probReal_univ, one_smul]
  have hG₀ (i : Fin N) : 0 ≤ meanG i := integral_nonneg fun env =>
    bestSwapGain_nonneg (q env) (u env) i
  have hsub (i : Fin N) (hi : i ∈ Aᶜ) : meanQ i / (184 * H ^ 5) ≤ meanG i := by
    refine tree_nonaux_expected_gain hh e active (monotone_blockLeaf h r) η pick hm anchor i ?_
    intro j hej
    exact (Finset.mem_compl.mp hi) (Finset.mem_map.mpr ⟨j, Finset.mem_univ _, hej⟩)
  have hother : ((T : ℝ) - ∑ i ∈ A, meanQ i) / (184 * H ^ 5) ≤ ∑ i ∈ Aᶜ, meanG i := by
    have hs := Finset.sum_le_sum (s := Aᶜ) (fun i hi => hsub i hi)
    rw [← Finset.sum_div] at hs
    have hsplit := A.sum_add_sum_compl meanQ
    rw [htotalQ] at hsplit
    have he : (∑ i ∈ Aᶜ, meanQ i) = (T : ℝ) - ∑ i ∈ A, meanQ i := by linarith only [hsplit]
    rwa [he] at hs
  have haux : (∑ i ∈ A, meanQ i) / (4 * H) - (T : ℝ) / (64 * H) ≤ ∑ i ∈ A, meanG i := by
    have hpoint (env : TreeEnvironment h M N T) :
        (∑ i ∈ A, Q i env) / (4 * H) - W env ≤ ∑ i ∈ A, G i env := by
      unfold A
      simp only [Finset.sum_map]
      exact tree_auxiliary_gain hh e active env.1.2.1 (tableLeafCoin env.1.1) env.1.2.2 (q env)
    have hi₁ : Integrable (fun env => (∑ i ∈ A, Q i env) / (4 * H)) P :=
      (integrable_finsetSum _ fun i _ => hQ i).div_const _
    have hi₂ : Integrable (fun env => ∑ i ∈ A, G i env) P :=
      integrable_finsetSum _ fun i _ => hG i
    have hs := integral_mono (hi₁.sub hW) hi₂ hpoint
    change (∫ env, (∑ i ∈ A, Q i env) / (4 * H) - W env ∂P) ≤ ∫ env, ∑ i ∈ A, G i env ∂P at hs
    rw [integral_sub hi₁ hW, integral_div, integral_finsetSum _ (fun i _ => hQ i),
      integral_finsetSum _ (fun i _ => hG i)] at hs
    have hw : (∫ env, W env ∂P) ≤ (T : ℝ) / (64 * H) :=
      (tree_expected_selected_hits (r := r) e η hη hη₁ pick hm anchor).trans hbudget
    change (∑ i ∈ A, meanQ i) / (4 * H) - (∫ env, W env ∂P) ≤ ∑ i ∈ A, meanG i at hs
    linarith only [hs, hw]
  have hH : 1 ≤ H := by unfold H treeHeight; linarith only [Nat.cast_nonneg (α := ℝ) h]
  have h := aggregate_swap_gain (Nat.cast_nonneg T) hH
    (Finset.sum_nonneg fun i _ => hG₀ i) (Finset.sum_nonneg fun i _ => hG₀ i) haux hother
  rw [Finset.sum_add_sum_compl A] at h
  rw [← integral_finsetSum _ (fun i _ => hG i)] at h
  simpa only [pseudoSwapRegret_eq_sum_bestSwapGain, G, u] using h

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open MeasureTheory Set Filter

theorem swapRegret_congr_before {N T : ℕ} {y y' : ℕ → Fin N → ℝ}
    {I I' : ℕ → Fin N}
    (hy : ∀ t < T, ∀ i, y t i = y' t i) (hI : ∀ t < T, I t = I' t) :
    swapRegret T y I = swapRegret T y' I' := by
  unfold swapRegret
  congr 1
  funext f
  exact Finset.sum_congr rfl fun t ht => by
    have ht' := Finset.mem_range.mp ht
    rw [hI t ht', hy t ht', hy t ht']

theorem integrable_swapRegret_of_bounded {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsFiniteMeasure P] {N T : ℕ} (y : X → ℕ → Fin N → ℝ) (I : X → ℕ → Fin N)
    (hy : ∀ t < T, ∀ i x, y x t i ∈ Icc 0 1)
    (hym : ∀ t < T, ∀ i, Measurable fun x => y x t i)
    (hIm : ∀ t < T, Measurable fun x => I x t) :
    Integrable (fun x => swapRegret T (y x) (I x)) P := by
  classical
  unfold swapRegret
  apply integrable_finset_max ⟨id, Finset.mem_univ _⟩ _ (B := T)
  · intro f
    exact Finset.measurable_sum _ fun t ht =>
      (measurable_select (hIm t (Finset.mem_range.mp ht)) (fun j => hym t (Finset.mem_range.mp ht) (f j))).sub
        (measurable_select (hIm t (Finset.mem_range.mp ht)) (hym t (Finset.mem_range.mp ht)))
  · intro f x
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      _ ≤ ∑ _ ∈ Finset.range T, (1 : ℝ) := Finset.sum_le_sum fun t ht => by
        have h₁ := hy t (Finset.mem_range.mp ht) (f (I x t)) x
        have h₂ := hy t (Finset.mem_range.mp ht) (I x t) x
        exact abs_le.mpr ⟨by linarith only [h₁.1, h₂.2], by linarith only [h₁.2, h₂.1]⟩
      _ = _ := by simp

/-- A jointly measurable policy and reward sequence induce measurable
actions and observation histories. -/
theorem measurable_feedbackHistory_of_measurable {S X : Type*}
    [MeasurableSpace S] [MeasurableSpace X] {N : ℕ}
    (pick : (t : ℕ) → S → FeedbackHistory t → Fin N)
    (hp : ∀ t, Measurable (fun p : S × FeedbackHistory t => pick t p.1 p.2))
    (seed : X → S) (hs : Measurable seed) (y : X → ℕ → Fin N → ℝ)
    (hy : ∀ t i, Measurable (fun x => y x t i)) (t : ℕ) :
    Measurable (fun x => feedbackHistory (fun n => pick n (seed x)) (y x) t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    change Measurable (fun x =>
      (feedbackHistory (fun n => pick n (seed x)) (y x) t,
        y x t (pick t (seed x) (feedbackHistory (fun n => pick n (seed x)) (y x) t))))
    apply ih.prodMk
    exact measurable_select ((hp t).comp (hs.prodMk ih)) (hy t)

set_option maxHeartbeats 900000 in
/-- Average the realized regret over the construction. The martingale
bound is used conditionally on the three finite tables. -/
theorem tree_environment_expected_regret {h M U N r : ℕ} [Nonempty (Fin M)] (hh : 0 < h)
    (e : Fin N ≃ TreeAction h M U) (η : ℝ) (hη : 0 < η) (hη₁ : η < 1)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (hm : ∀ t, Measurable (pick t)) (anchor : Fin N)
    (hbudget : ((2 ^ h : ℕ) : ℝ) * ((r : ℝ) / M + η * r * Real.sqrt ((r : ℝ) / (6 * M))) ≤
      ((2 ^ h * r : ℕ) : ℝ) / (64 * treeHeight h)) :
    let T := 2 ^ h * r
    let active := blockLeaf h r
    let P := treeEnvironmentLaw h M N T
    η / 48 * ((T : ℝ) / (368 * treeHeight h ^ 5)) -
      N * (η / 16 * Real.sqrt (2 * T * Real.log (2 * N))) ≤
      ∫ env, swapRegret T (treeEnvironmentReward e active η env)
        (treeEnvironmentAction e active η pick anchor env) ∂P := by
  classical
  intro T active P
  let C := TreeTables h M T
  let μ := finiteTableLaw C
  let ν := rewardTapeLaw N T
  let q := treeEnvironmentPlay (T := T) e active η pick anchor
  let y := treeEnvironmentReward (T := T) e active η
  let I := treeEnvironmentAction (T := T) e active η pick anchor
  let u (env : TreeEnvironment h M N T) := tableBonuses e active env.1
  let G (env : C × RewardTape N T) := pseudoSwapRegret T (q env) (u env)
  let R (env : C × RewardTape N T) := swapRegret T (y env) (I env)
  let err := N * (η / 16 * Real.sqrt (2 * T * Real.log (2 * N)))
  have hG : Integrable G (μ.prod ν) := by
    unfold G
    simp only [pseudoSwapRegret_eq_sum_bestSwapGain]
    exact integrable_finsetSum _ (fun i _ => integrable_treeEnvironmentBestGain e active η pick hm anchor i)
  have hR : Integrable R (μ.prod ν) :=
    integrable_swapRegret_of_bounded (μ.prod ν) y I
      (fun t _ i env => boundedRoundReward_mem hη.le hη₁.le (u env t i) i (tapeDraw env.2 t))
      (fun t _ i => measurable_treeEnvironmentReward e active η t i)
      (fun t _ => measurable_treeEnvironmentAction e active η pick hm anchor t)
  have hpoint (c : C) :
      η / 48 * (∫ tape, G (c, tape) ∂ν) - err ≤ ∫ tape, R (c, tape) ∂ν := by
    let u' := tableBonuses e active c
    let pick' (t : ℕ) (pre : RewardTape N t) := pick t (rawTapeHistory η u' pick t pre)
    have hu' (t : ℕ) (_ht : t < T) (i : Fin N) : u' t i ∈ Icc 0 1 := treeBonusProb_mem _ _ _ _ _
    have hp' (t : ℕ) (_ht : t < T) : Measurable (pick' t) :=
      (hm t).comp (measurable_rawTapeHistory η u' pick hm t)
    have hb := expected_tape_swap_lower anchor hη hη₁.le u' hu' pick' hp'
    let y' (ω : RewardTape N T) (t : ℕ) (i : Fin N) : ℝ :=
      if ht : t < T then boundedRoundReward η (u' t i) i (rewardTapePrefix N (Nat.succ_le_of_lt ht) ω).2
      else 0
    have hy (tape : RewardTape N T) (t : ℕ) (ht : t < T) (i : Fin N) : y' tape t i = y (c, tape) t i := by
      simp only [y', y, treeEnvironmentReward, tapeDraw, dif_pos ht]
      rfl
    have hrewrite (tape : RewardTape N T) :
        swapRegret T (y' tape) (I (c, tape)) = R (c, tape) :=
      swapRegret_congr_before (hy tape) (fun _ _ => rfl)
    change η / 48 * (∫ tape, G (c, tape) ∂ν) - err ≤
      ∫ tape, swapRegret T (y' tape) (I (c, tape)) ∂ν at hb
    simpa only [hrewrite] using hb
  have hs := integral_mono ((hG.integral_prod_left.const_mul (η / 48)).sub (integrable_const err))
    hR.integral_prod_left hpoint
  change (∫ c, η / 48 * (∫ tape, G (c, tape) ∂ν) - err ∂μ) ≤
    ∫ c, (∫ tape, R (c, tape) ∂ν) ∂μ at hs
  rw [integral_sub (hG.integral_prod_left.const_mul (η / 48)) (integrable_const err),
    integral_const_mul, integral_const, probReal_univ, one_smul,
    ← integral_prod G hG, ← integral_prod R hR] at hs
  have hproxy : (T : ℝ) / (368 * treeHeight h ^ 5) ≤ ∫ env, G env ∂μ.prod ν :=
    tree_expected_proxy hh e η hη.le hη₁ pick hm anchor hbudget
  exact (sub_le_sub_right (mul_le_mul_of_nonneg_left hproxy (by positivity)) _).trans hs

/-- For a randomized learner, the lower bound yields a single fixed choice
of the tables and tape, hence an oblivious deterministic reward sequence. -/
theorem exists_tree_environment {S : Type*} [MeasurableSpace S] (P : Measure S)
    [IsProbabilityMeasure P]
    {h M U N r : ℕ} [Nonempty (Fin M)] (hh : 0 < h)
    (e : Fin N ≃ TreeAction h M U) (η : ℝ) (hη : 0 < η) (hη₁ : η < 1)
    (pick : (t : ℕ) → S → FeedbackHistory t → Fin N)
    (hm : ∀ t, Measurable (fun p : S × FeedbackHistory t => pick t p.1 p.2)) (anchor : Fin N)
    (hbudget : ((2 ^ h : ℕ) : ℝ) * ((r : ℝ) / M + η * r * Real.sqrt ((r : ℝ) / (6 * M))) ≤
      ((2 ^ h * r : ℕ) : ℝ) / (64 * treeHeight h)) :
    let T := 2 ^ h * r
    let active := blockLeaf h r
    ∃ env : TreeEnvironment h M N T,
      η / 48 * ((T : ℝ) / (368 * treeHeight h ^ 5)) -
        N * (η / 16 * Real.sqrt (2 * T * Real.log (2 * N))) ≤
        ∫ s, swapRegret T (treeEnvironmentReward e active η env)
          (treeEnvironmentAction e active η (fun t => pick t s) anchor env) ∂P := by
  intro T active
  let C := TreeEnvironment h M N T
  let μ := treeEnvironmentLaw h M N T
  let y := treeEnvironmentReward (T := T) e active η
  let I (p : C × S) (t : ℕ) := treeEnvironmentAction e active η (fun n => pick n p.2) anchor p.1 t
  have hIm (t : ℕ) (ht : t < T) : Measurable (fun p => I p t) := by
    have hhist := measurable_feedbackHistory_of_measurable pick hm Prod.snd measurable_snd
      (fun p : C × S => y p.1)
      (fun t i => (measurable_treeEnvironmentReward e active η t i).comp measurable_fst) t
    have he : (fun p => I p t) =
        fun p : C × S => pick t p.2 (feedbackHistory (fun n => pick n p.2) (y p.1) t) := by
      funext p
      simp only [I, treeEnvironmentAction, dif_pos ht]
      rw [rawTapeHistory_eq_feedbackHistory]
      rfl
    rw [he]
    exact (hm t).comp (measurable_snd.prodMk hhist)
  let R (p : C × S) := swapRegret T (y p.1) (I p)
  have hR : Integrable R (μ.prod P) :=
    integrable_swapRegret_of_bounded (μ.prod P) (fun p : C × S => y p.1) I
      (fun t _ i p => boundedRoundReward_mem hη.le hη₁.le (tableBonuses e active p.1.1 t i) i (tapeDraw p.1.2 t))
      (fun t _ i => (measurable_treeEnvironmentReward e active η t i).comp measurable_fst) hIm
  refine exists_environment_of_seedwise_lower_bound μ P R hR (fun s => ?_)
  exact tree_environment_expected_regret hh e η hη hη₁ (fun t => pick t s)
    (fun t => (hm t).comp measurable_prodMk_left) anchor hbudget

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open MeasureTheory Set Filter

theorem treeBonusScale_pos (h : ℕ) : 0 < treeBonusScale h := by unfold treeBonusScale treeActionBudget treeHeight; positivity

theorem treeBonusScale_lt_one (h : ℕ) : treeBonusScale h < 1 := by
  unfold treeBonusScale
  have hk : (16 : ℝ) ≤ treeActionBudget h := by
    unfold treeActionBudget
    have hpow : 0 < (2 : ℕ) ^ h := by positivity
    exact_mod_cast (show 16 ≤ 16 * 2 ^ h by omega)
  have hh : 1 ≤ treeHeight h := by unfold treeHeight; linarith only [Nat.cast_nonneg (α := ℝ) h]
  apply (div_lt_one (by positivity)).mpr
  nlinarith only [hk, hh, mul_nonneg (show 0 ≤ (treeActionBudget h : ℝ) by positivity) (sub_nonneg.mpr hh)]

/-- A hard environment at the dyadic horizon, also allowing extra unnamed
actions in the learner's action space. -/
theorem exists_hard_tree_environment {S : Type*} [MeasurableSpace S] (P : Measure S)
    [IsProbabilityMeasure P]
    {K₀ h N U : ℕ} (hh : 0 < h) (hKN : treeActionBudget h ≤ N) (hNK : N ≤ 2 * treeActionBudget h)
    (hK₀ : K₀ ≤ treeActionBudget h)
    (hscale : ∀ h N : ℕ,
      K₀ ≤ treeActionBudget h → treeActionBudget h ≤ N → N ≤ 2 * treeActionBudget h →
      let L := 2 ^ h
      let M : ℕ := 8 * L
      let r := treePeriodLength h
      let T := L * r
      let H := treeHeight h
      let η := treeBonusScale h
      ((L : ℝ) * ((r : ℝ) / M + η * r * Real.sqrt ((r : ℝ) / (6 * M))) ≤
        (T : ℝ) / (64 * H)) ∧
      ((N : ℝ) ^ 3 / (8 * 10 ^ 10 * (Real.log N) ^ 6) ≤
        η / 48 * ((T : ℝ) / (368 * H ^ 5)) -
          N * (η / 16 * Real.sqrt (2 * T * Real.log (2 * N)))))
    (e : Fin N ≃ TreeAction h (8 * 2 ^ h) U) (pick : (t : ℕ) → S → FeedbackHistory t → Fin N)
    (hm : ∀ t, Measurable (fun p : S × FeedbackHistory t => pick t p.1 p.2)) (anchor : Fin N) :
    let r := treePeriodLength h
    let T := 2 ^ h * r
    let active := blockLeaf h r
    let η := treeBonusScale h
    ∃ env : TreeEnvironment h (8 * 2 ^ h) N T,
      (N : ℝ) ^ 3 / (8 * 10 ^ 10 * (Real.log N) ^ 6) ≤
        ∫ s, swapRegret T (treeEnvironmentReward e active η env)
          (treeEnvironmentAction e active η (fun t => pick t s) anchor env) ∂P := by
  intro r T active η
  have _ : Nonempty (Fin (8 * 2 ^ h)) := ⟨⟨0, by positivity⟩⟩
  obtain ⟨hb, hr⟩ := hscale h N hK₀ hKN hNK
  obtain ⟨env, he⟩ := exists_tree_environment (r := r) P hh e η (treeBonusScale_pos h)
    (treeBonusScale_lt_one h) pick hm anchor hb
  exact ⟨env, hr.trans he⟩

end CalibeatBandit

end

theorem solution : type_of% @CalibeatBandit.exists_hard_tree_environment := @CalibeatBandit.exists_hard_tree_environment
