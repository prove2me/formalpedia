-- Prove2me | solution 1 for CohenPriceFairness.LocalWelfare.lemma_1
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-29T07:49:46.595997+00:00
-- url     : https://prove2.me/submissions/6141345e-eca8-4322-836e-61cdc92601f8

import Mathlib
import Definitions.Def_CohenPriceFairness_LocalWelfare_Sensitivity

open MeasureTheory Filter Topology Set

namespace D75S226

open CohenPriceFairness.LocalWelfare

noncomputable def law (a d c L U : ℝ) : Measure ℝ :=
  ENNReal.ofReal a • Measure.dirac d + ENNReal.ofReal c • volume.restrict (Icc L U)

section gen
variable {a d c L U : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hdL : d < L) (hLU : L < U)
include ha hc hdL hLU

lemma law_apply (s : Set ℝ) (hs : MeasurableSet s) :
    (law a d c L U s).toReal = a * s.indicator 1 d + c * (volume (s ∩ Icc L U)).toReal := by
  unfold law
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, Measure.dirac_apply' _ hs,
    Measure.restrict_apply hs]
  have hfin : volume (s ∩ Icc L U) ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
      (measure_mono inter_subset_right)
  have hind : s.indicator 1 d ≠ (⊤ : ENNReal) := by
    by_cases h : d ∈ s <;> simp [h]
  rw [smul_eq_mul, smul_eq_mul, ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hind)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin), ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hc]
  congr 2
  by_cases h : d ∈ s <;> simp [h]

lemma law_univ : law a d c L U univ = ENNReal.ofReal (a + c * (U - L)) := by
  unfold law
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, measure_univ,
    Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Icc, smul_eq_mul,
    smul_eq_mul, mul_one, ← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_add ha
    (mul_nonneg hc (by linarith))]

lemma vol_Ici (p : ℝ) : (volume (Ici p ∩ Icc L U)).toReal = max (U - max p L) 0 := by
  have e : Ici p ∩ Icc L U = Icc (max p L) U := by
    ext v; simp only [mem_inter_iff, mem_Ici, mem_Icc, max_le_iff]; tauto
  rw [e, Real.volume_Icc, ENNReal.toReal_ofReal']

lemma demand_eq (p : ℝ) :
    (law a d c L U (Ici p)).toReal = a * (if p ≤ d then 1 else 0) + c * max (U - max p L) 0 := by
  rw [law_apply ha hc hdL hLU _ measurableSet_Ici, vol_Ici ha hc hdL hLU]
  by_cases h : p ≤ d
  · simp [indicator, h]
  · simp [indicator, h]

lemma int_dirac (f : ℝ → ℝ) : Integrable f (Measure.dirac d) := by
  have := ae_eq_dirac (a := d) f
  exact (integrable_const (f d)).congr this.symm

lemma surplus_eq (p : ℝ) :
    ∫ v, max (v - p) 0 ∂(law a d c L U) =
      a * max (d - p) 0 + c * ∫ v in L..U, max (v - p) 0 := by
  unfold law
  have hi : Integrable (fun v : ℝ => max (v - p) 0) (volume.restrict (Icc L U)) :=
    (by fun_prop : Continuous (fun v : ℝ => max (v - p) 0)).integrableOn_Icc
  rw [integral_add_measure ((int_dirac ha hc hdL hLU _).smul_measure ENNReal.ofReal_ne_top)
    (hi.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    integral_dirac, ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hc,
    intervalIntegral.integral_of_le hLU.le, integral_Icc_eq_integral_Ioc]
  simp [smul_eq_mul]

lemma iint_low (p : ℝ) (hp : p ≤ L) :
    ∫ v in L..U, max (v - p) 0 = (U ^ 2 - L ^ 2) / 2 - p * (U - L) := by
  have : ∫ v in L..U, max (v - p) 0 = ∫ v in L..U, (v - p) := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hLU.le] at hv
    simp only
    rw [max_eq_left (by linarith [hv.1])]
  rw [this, intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_id
    intervalIntegrable_const, integral_id, intervalIntegral.integral_const, smul_eq_mul]
  ring

lemma iint_mid (p : ℝ) (hp1 : L ≤ p) (hp2 : p ≤ U) :
    ∫ v in L..U, max (v - p) 0 = (U - p) ^ 2 / 2 := by
  have hint : ∀ x y : ℝ, IntervalIntegrable (fun v : ℝ => max (v - p) 0) volume x y :=
    fun x y => (by fun_prop : Continuous (fun v : ℝ => max (v - p) 0)).intervalIntegrable _ _
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint L p) (hint p U)]
  have e1 : ∫ v in L..p, max (v - p) 0 = ∫ v in L..p, (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hp1] at hv
    simp only
    rw [max_eq_right (by linarith [hv.2])]
  have e2 : ∫ v in p..U, max (v - p) 0 = ∫ v in p..U, (v - p) := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hp2] at hv
    simp only
    rw [max_eq_left (by linarith [hv.1])]
  rw [e1, e2, intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_id
    intervalIntegrable_const, integral_id, intervalIntegral.integral_const,
    intervalIntegral.integral_const, smul_eq_mul, smul_eq_mul]
  ring

lemma below_mass (p : ℝ) (hp1 : L ≤ p) (hp2 : p ≤ U) :
    (law a d c L U (Iio p)).toReal = a + c * (p - L) := by
  rw [law_apply ha hc hdL hLU _ measurableSet_Iio]
  have hd : d ∈ Iio p := by simp; linarith
  have e : Iio p ∩ Icc L U = Ico L p := by
    ext v; simp; constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith⟩
  rw [e, Real.volume_Ico, ENNReal.toReal_ofReal (by linarith)]
  simp [indicator, hd]

lemma below_int (p : ℝ) (hp1 : L ≤ p) (hp2 : p ≤ U) :
    ∫ v in Iio p, v ∂(law a d c L U) = a * d + c * ((p ^ 2 - L ^ 2) / 2) := by
  unfold law
  rw [Measure.restrict_add, Measure.restrict_smul, Measure.restrict_smul,
    Measure.restrict_restrict measurableSet_Iio]
  have hd : d ∈ Iio p := by simp; linarith
  rw [restrict_dirac' measurableSet_Iio, if_pos hd]
  have e : Iio p ∩ Icc L U = Ico L p := by
    ext v; simp; constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith⟩
  rw [e]
  have hi : Integrable (fun v : ℝ => v) (volume.restrict (Ico L p)) :=
    (continuous_id.integrableOn_Icc (a := L) (b := p)).mono_set Ico_subset_Icc_self
  rw [integral_add_measure ((int_dirac ha hc hdL hLU _).smul_measure ENNReal.ofReal_ne_top)
    (hi.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    integral_dirac, ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hc,
    integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hp1, integral_id]
  simp [smul_eq_mul]

end gen

lemma vlaw {a d c L U : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hdL : d < L) (hLU : L < U)
    (hd : 0 ≤ d ∨ a = 0) (hL : 0 ≤ L) (h1 : a + c * (U - L) = 1) :
    ValuationLaw (law a d c L U) := by
  refine ⟨⟨by rw [law_univ ha hc hdL hLU, h1, ENNReal.ofReal_one]⟩, ?_, ?_⟩
  · unfold law
    rw [ae_add_measure_iff]
    constructor
    · rcases hd with hd | hd
      · refine Measure.ae_smul_measure ?_ _
        rw [ae_dirac_iff measurableSet_Ici]; exact hd
      · rw [hd, ENNReal.ofReal_zero, zero_smul]; simp
    · refine Measure.ae_smul_measure ?_ _
      apply (ae_restrict_iff' measurableSet_Icc).2
      exact Filter.Eventually.of_forall (fun v hv => le_trans hL hv.1)
  · unfold law
    have hi : Integrable (fun v : ℝ => v) (volume.restrict (Icc L U)) :=
      continuous_id.integrableOn_Icc
    exact ((int_dirac ha hc hdL hLU _).smul_measure ENNReal.ofReal_ne_top).add_measure
      (hi.smul_measure ENNReal.ofReal_ne_top)

lemma twice_of_eqOn {f g : ℝ → ℝ} {l u x : ℝ} (hx : x ∈ Ioo l u) (h : EqOn f g (Ioo l u))
    (hg : ContDiffOn ℝ 2 g (Ioo l u)) : TwiceDifferentiableAt f x := by
  have hf : ContDiffOn ℝ 2 f (Ioo l u) := hg.congr h
  have hf' := (contDiffOn_succ_iff_deriv_of_isOpen (n := 1) isOpen_Ioo).1 hf
  refine ⟨?_, ?_⟩
  · filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact (hf'.1 y hy).differentiableAt (isOpen_Ioo.mem_nhds hy)
  · exact (hf'.2.2.differentiableOn (by norm_num) x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)

lemma active_of {f : ℝ → ℝ} {l u x : ℝ} (hx : x ∈ Ioo l u)
    (h : StrictMonoOn f (Ioo l u) ∨ StrictAntiOn f (Ioo l u)) : ActiveInvertible f x := by
  have hinj : InjOn f (Ioo l u) := by
    rcases h with h | h
    · exact h.injOn
    · exact h.injOn
  refine ⟨l, u, hx.1, hx.2, ?_, Function.invFunOn f (Ioo l u), ?_, ?_⟩
  · rcases h with h | h
    · exact Or.inl h.monotoneOn
    · exact Or.inr h.antitoneOn
  · intro p hp
    exact hinj (Function.invFunOn_mem ⟨p, hp, rfl⟩) hp (Function.invFunOn_eq ⟨p, hp, rfl⟩)
  · intro y hy
    exact ⟨Function.invFunOn_mem hy, Function.invFunOn_eq hy⟩

noncomputable def μ0 : Measure ℝ := law 0 (-1) 1 0 1
noncomputable def μ1 : Measure ℝ := law (1 / 2) (2 / 3) (1 / 6) 1 4

noncomputable def mkt : Market := ⟨![μ0, μ1], fun _ => 1, 0⟩

lemma dem0 (p : ℝ) : demand mkt 0 p = max (1 - max p 0) 0 := by
  show (μ0 (Ici p)).toReal = _
  unfold μ0; rw [demand_eq (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; ring

lemma dem1 (p : ℝ) : demand mkt 1 p =
    1 / 2 * (if p ≤ 2 / 3 then 1 else 0) + 1 / 6 * max (4 - max p 1) 0 := by
  show (μ1 (Ici p)).toReal = _
  unfold μ1; rw [demand_eq (by norm_num) (by norm_num) (by norm_num) (by norm_num)]

lemma prof (i : Fin 2) (p : ℝ) : profit mkt i p = p * demand mkt i p := by
  simp [profit, mkt]

lemma prof0_le (p : ℝ) (hp : 0 ≤ p) : profit mkt 0 p ≤ 1 / 4 := by
  rw [prof, dem0, max_eq_left hp]
  rcases le_total p 1 with h | h
  · rw [max_eq_left (by linarith)]; nlinarith [sq_nonneg (p - 1 / 2)]
  · rw [max_eq_right (by linarith)]; norm_num

lemma prof1_le (p : ℝ) (hp : 0 ≤ p) : profit mkt 1 p ≤ 2 / 3 := by
  rw [prof, dem1]
  by_cases h1 : p ≤ 2 / 3
  · rw [if_pos h1, max_eq_right (show p ≤ 1 by linarith)]; norm_num; linarith
  · rw [if_neg h1]
    rcases le_total p 1 with h2 | h2
    · rw [max_eq_right h2]; norm_num; linarith
    · rw [max_eq_left h2]
      rcases le_total p 4 with h3 | h3
      · rw [max_eq_left (show 0 ≤ 4 - p by linarith)]; nlinarith [sq_nonneg (p - 2)]
      · rw [max_eq_right (show 4 - p ≤ 0 by linarith)]; norm_num

lemma prof0_half : profit mkt 0 (1 / 2) = 1 / 4 := by
  rw [prof, dem0]; norm_num
lemma prof1_two : profit mkt 1 2 = 2 / 3 := by
  rw [prof, dem1]; norm_num
lemma prof1_23 : profit mkt 1 (2 / 3) = 2 / 3 := by
  rw [prof, dem1]; norm_num

lemma sur1 (p : ℝ) : surplus mkt 1 p =
    1 / 2 * max (2 / 3 - p) 0 + 1 / 6 * ∫ v in (1 : ℝ)..4, max (v - p) 0 := by
  show ∫ v, max (v - p) 0 ∂μ1 = _
  unfold μ1; rw [surplus_eq (by norm_num) (by norm_num) (by norm_num) (by norm_num)]

lemma sur0 (p : ℝ) : surplus mkt 0 p = ∫ v in (0 : ℝ)..1, max (v - p) 0 := by
  show ∫ v, max (v - p) 0 ∂μ0 = _
  unfold μ0; rw [surplus_eq (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; ring

lemma sur1_23 : surplus mkt 1 (2 / 3) = 11 / 12 := by
  rw [sur1, iint_low (a := 1/2) (d := 2/3) (c := 1/6) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) _ (by norm_num)]; norm_num
lemma sur1_two : surplus mkt 1 2 = 1 / 3 := by
  rw [sur1, iint_mid (a := 1/2) (d := 2/3) (c := 1/6) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) _ (by norm_num) (by norm_num)]; norm_num

lemma nb0 (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) : nonbuyer mkt 0 p = p / 2 := by
  have hm : (μ0 (Iio p)).toReal = p := by
    unfold μ0; rw [below_mass (by norm_num) (by norm_num) (by norm_num) (by norm_num) _
      (by linarith [hp.1]) (by linarith [hp.2])]; ring
  have hi : ∫ v in Iio p, v ∂μ0 = p ^ 2 / 2 := by
    unfold μ0; rw [below_int (by norm_num) (by norm_num) (by norm_num) (by norm_num) _
      (by linarith [hp.1]) (by linarith [hp.2])]; ring
  show (if μ0 (Iio p) = 0 then 0 else (∫ v in Iio p, v ∂μ0) / (μ0 (Iio p)).toReal) = _
  have hne : μ0 (Iio p) ≠ 0 := by
    intro h; rw [h] at hm; simp at hm; linarith [hp.1]
  rw [if_neg hne, hm, hi]
  have := hp.1
  field_simp

lemma nb1 (p : ℝ) (hp : p ∈ Ioo (1 : ℝ) 4) :
    nonbuyer mkt 1 p = (p ^ 2 + 3) / (2 * (p + 2)) := by
  have hm : (μ1 (Iio p)).toReal = 1 / 2 + 1 / 6 * (p - 1) := by
    unfold μ1; rw [below_mass (by norm_num) (by norm_num) (by norm_num) (by norm_num) _
      (by linarith [hp.1]) (by linarith [hp.2])]
  have hi : ∫ v in Iio p, v ∂μ1 = 1 / 2 * (2 / 3) + 1 / 6 * ((p ^ 2 - 1 ^ 2) / 2) := by
    unfold μ1; rw [below_int (by norm_num) (by norm_num) (by norm_num) (by norm_num) _
      (by linarith [hp.1]) (by linarith [hp.2])]
  show (if μ1 (Iio p) = 0 then 0 else (∫ v in Iio p, v ∂μ1) / (μ1 (Iio p)).toReal) = _
  have hne : μ1 (Iio p) ≠ 0 := by
    intro h; rw [h] at hm; simp at hm; linarith [hp.1]
  rw [if_neg hne, hm, hi]
  have := hp.1
  field_simp; ring

noncomputable def bb : Prices := ![1 / 2, 2]

lemma hadm : mkt.Admissible := by
  refine ⟨le_rfl, fun i => ⟨by simp [mkt], ?_⟩⟩
  fin_cases i
  · exact vlaw (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inr rfl) le_rfl
      (by norm_num)
  · exact vlaw (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
      (by norm_num) (by norm_num)

lemma hbase : BaselineOptimal mkt bb := by
  intro i; fin_cases i
  · refine ⟨by simp [bb], fun p hp => ?_⟩
    show profit mkt 0 p ≤ profit mkt 0 (1 / 2)
    rw [prof0_half]; exact prof0_le p hp
  · refine ⟨by simp [bb], fun p hp => ?_⟩
    show profit mkt 1 p ≤ profit mkt 1 2
    rw [prof1_two]; exact prof1_le p hp

lemma hreg : LemmaRegularity mkt bb := by
  intro i; fin_cases i
  · show TwiceDifferentiableAt (demand mkt 0) (1 / 2) ∧ TwiceDifferentiableAt (surplus mkt 0) (1 / 2) ∧
      TwiceDifferentiableAt (nonbuyer mkt 0) (1 / 2) ∧ TwiceDifferentiableAt (profit mkt 0) (1 / 2) ∧
      ActiveInvertible (demand mkt 0) (1 / 2) ∧ ActiveInvertible (surplus mkt 0) (1 / 2) ∧
      ActiveInvertible (nonbuyer mkt 0) (1 / 2)
    have hx : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by norm_num
    have ed : EqOn (demand mkt 0) (fun p => 1 - p) (Ioo 0 1) := by
      intro p hp; rw [dem0, max_eq_left hp.1.le, max_eq_left (by linarith [hp.2])]
    have es : EqOn (surplus mkt 0) (fun p => (1 - p) ^ 2 / 2) (Ioo 0 1) := by
      intro p hp; rw [sur0, iint_mid (a := 0) (d := -1) (c := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) _ hp.1.le hp.2.le]
    have en : EqOn (nonbuyer mkt 0) (fun p => p / 2) (Ioo 0 1) := fun p hp => nb0 p hp
    have ep : EqOn (profit mkt 0) (fun p => p * (1 - p)) (Ioo 0 1) := by
      intro p hp; rw [prof, ed hp]
    refine ⟨twice_of_eqOn hx ed (by fun_prop), twice_of_eqOn hx es (by fun_prop),
      twice_of_eqOn hx en (by fun_prop), twice_of_eqOn hx ep (by fun_prop), ?_, ?_, ?_⟩
    · exact active_of hx (Or.inr fun x hx' y hy hxy => by rw [ed hx', ed hy]; linarith)
    · exact active_of hx (Or.inr fun x hx' y hy hxy => by
        rw [es hx', es hy]; nlinarith [hx'.2, hy.2])
    · exact active_of hx (Or.inl fun x hx' y hy hxy => by rw [en hx', en hy]; linarith)
  · show TwiceDifferentiableAt (demand mkt 1) 2 ∧ TwiceDifferentiableAt (surplus mkt 1) 2 ∧
      TwiceDifferentiableAt (nonbuyer mkt 1) 2 ∧ TwiceDifferentiableAt (profit mkt 1) 2 ∧
      ActiveInvertible (demand mkt 1) 2 ∧ ActiveInvertible (surplus mkt 1) 2 ∧
      ActiveInvertible (nonbuyer mkt 1) 2
    have hx : (2 : ℝ) ∈ Ioo (1 : ℝ) 4 := by norm_num
    have ed : EqOn (demand mkt 1) (fun p => 1 / 6 * (4 - p)) (Ioo 1 4) := by
      intro p hp
      rw [dem1, if_neg (by linarith [hp.1]), max_eq_left hp.1.le, max_eq_left (by linarith [hp.2])]
      ring
    have es : EqOn (surplus mkt 1) (fun p => 1 / 6 * ((4 - p) ^ 2 / 2)) (Ioo 1 4) := by
      intro p hp
      rw [sur1, iint_mid (a := 1/2) (d := 2/3) (c := 1/6) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) _ hp.1.le hp.2.le, max_eq_right (by linarith [hp.1])]
      ring
    have en : EqOn (nonbuyer mkt 1) (fun p => (p ^ 2 + 3) / (2 * (p + 2))) (Ioo 1 4) :=
      fun p hp => nb1 p hp
    have ep : EqOn (profit mkt 1) (fun p => p * (1 / 6 * (4 - p))) (Ioo 1 4) := by
      intro p hp; rw [prof, ed hp]
    have hcn : ContDiffOn ℝ 2 (fun p : ℝ => (p ^ 2 + 3) / (2 * (p + 2))) (Ioo 1 4) := by
      apply ContDiffOn.div (by fun_prop) (by fun_prop)
      intro x hx'; have := hx'.1; positivity
    refine ⟨twice_of_eqOn hx ed (by fun_prop), twice_of_eqOn hx es (by fun_prop),
      twice_of_eqOn hx en hcn, twice_of_eqOn hx ep (by fun_prop), ?_, ?_, ?_⟩
    · exact active_of hx (Or.inr fun x hx' y hy hxy => by rw [ed hx', ed hy]; linarith)
    · exact active_of hx (Or.inr fun x hx' y hy hxy => by
        rw [es hx', es hy]; nlinarith [hx'.2, hy.2])
    · exact active_of hx (Or.inl fun x hx' y hy hxy => by
        rw [en hx', en hy]
        have h1 := hx'.1; have h2 := hy.1
        rw [div_lt_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_pos (sub_pos.2 hxy) (show 0 < x * y + 2 * (x + y) - 3 by nlinarith)])

noncomputable def PP : ℝ → Prices := fun α => if α = 0 then bb else ![1 / 2, 2 / 3]

lemma tp_le (q : Prices) (hq : ∀ i, 0 ≤ q i) : totalProfit mkt q ≤ 1 / 4 + 2 / 3 := by
  unfold totalProfit
  linarith [prof0_le _ (hq 0), prof1_le _ (hq 1)]

lemma hsel : LocalOptimalSelection mkt bb .price PP := by
  refine ⟨by simp [PP], 1 / 2, by norm_num, by norm_num, fun α hα => ?_⟩
  have hgapb : gap mkt .price bb = 3 / 2 := by
    simp [gap, metricValue, bb]; norm_num [abs_of_neg]
  by_cases h0 : α = 0
  · subst h0
    simp only [PP, if_pos rfl]
    refine ⟨⟨by norm_num, fun i => (hbase i).1, by simp⟩, fun q hq => ?_⟩
    have := tp_le q hq.2.1
    unfold totalProfit at this ⊢
    show _ ≤ profit mkt 0 (1 / 2) + profit mkt 1 2
    rw [prof0_half, prof1_two]; linarith
  · simp only [PP, if_neg h0]
    refine ⟨⟨⟨hα.1, by linarith [hα.2]⟩, ?_, ?_⟩, fun q hq => ?_⟩
    · intro i; fin_cases i <;> simp <;> norm_num
    · rw [hgapb]; simp [gap, metricValue]; norm_num [abs_of_neg]; linarith [hα.2]
    · have := tp_le q hq.2.1
      unfold totalProfit at this ⊢
      show _ ≤ profit mkt 0 (1 / 2) + profit mkt 1 (2 / 3)
      rw [prof0_half, prof1_23]; linarith

lemma no_rd (D : ℝ) : ¬ RightDerivative (fun α => welfare mkt (PP α)) D := by
  intro h
  have e : ∀ α : ℝ, α ≠ 0 → welfare mkt (PP α) - welfare mkt (PP 0) = 7 / 12 := by
    intro α hα
    simp only [PP, if_neg hα, if_pos rfl, welfare, totalProfit, bb]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [prof1_23, prof1_two, sur1_23, sur1_two]
    simp [mkt]; norm_num
  have ht : Tendsto (fun α : ℝ => (welfare mkt (PP α) - welfare mkt (PP 0)) / α)
      (𝓝[>] 0) atTop := by
    have : Tendsto (fun α : ℝ => 7 / 12 * α⁻¹) (𝓝[>] 0) atTop :=
      tendsto_inv_nhdsGT_zero.const_mul_atTop (by norm_num)
    apply this.congr'
    filter_upwards [self_mem_nhdsWithin] with α hα
    rw [e α (ne_of_gt hα)]; ring
  exact not_tendsto_nhds_of_tendsto_atTop ht D h

end D75S226

open CohenPriceFairness.LocalWelfare D75S226 in
theorem solution : ¬ (∀ (m : Market) (hm : m.Admissible) (b : Prices)
    (hb : BaselineOptimal m b) (hr : LemmaRegularity m b),
    (b 0 < b 1 → SensitivityClaim m b .price (fun D =>
      (0 < D ↔
        m.population 1 * demand m 1 (b 1) * deriv (deriv (profit m 0)) (b 0) -
        m.population 0 * demand m 0 (b 0) * deriv (deriv (profit m 1)) (b 1) < 0))) ∧
    (demand m 0 (b 0) < demand m 1 (b 1) → SensitivityClaim m b .demand (fun D =>
      (0 < D ↔
        m.population 1 * demand m 1 (b 1) * deriv (demand m 1) (b 1) *
          deriv (deriv (profit m 0)) (b 0) -
        m.population 0 * demand m 0 (b 0) * deriv (demand m 0) (b 0) *
          deriv (deriv (profit m 1)) (b 1) < 0))) ∧
    (surplus m 0 (b 0) < surplus m 1 (b 1) → SensitivityClaim m b .surplus (fun D =>
      (0 < D ↔
        m.population 1 * (demand m 1 (b 1)) ^ 2 * deriv (deriv (profit m 0)) (b 0) -
        m.population 0 * (demand m 0 (b 0)) ^ 2 * deriv (deriv (profit m 1)) (b 1) > 0))) ∧
    (nonbuyer m 0 (b 0) < nonbuyer m 1 (b 1) → SensitivityClaim m b .nonbuyer (fun D =>
      (0 < D ↔
        m.population 1 * demand m 1 (b 1) * deriv (nonbuyer m 1) (b 1) *
          deriv (deriv (profit m 0)) (b 0) -
        m.population 0 * demand m 0 (b 0) * deriv (nonbuyer m 0) (b 0) *
          deriv (deriv (profit m 1)) (b 1) < 0)))) := by
  intro h
  have h1 := (h mkt hadm bb hbase hreg).1 (by simp [bb]; norm_num)
  obtain ⟨D, hD, -⟩ := h1.2 PP hsel
  exact no_rd D hD
