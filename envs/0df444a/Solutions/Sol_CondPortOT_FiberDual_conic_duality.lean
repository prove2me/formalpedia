-- Prove2me | solution 1 for CondPortOT.FiberDual.conic_duality
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T04:14:42.854146+00:00
-- url     : https://prove2.me/submissions/8c1d546f-8a86-48d0-b60e-0d0fb3077673

import Mathlib
import Definitions.Def_CondPortOT_FiberDual_Setting
open MeasureTheory RWPI.SqrtLasso ModelRiskOT.Duality
open scoped Pointwise

namespace CondPortOTConicAux

lemma extIntegral_eq_integral {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)
    (L : Y → ℝ) (hLi : Integrable L μ) :
    extIntegral μ (fun y => (L y : EReal)) = ((∫ y, L y ∂μ : ℝ) : EReal) := by
  have h1 : ∀ y, ((L y : EReal)).toENNReal = ENNReal.ofReal (L y) := fun y => by
    rw [EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
  have h2 : ∀ y, (-(L y : EReal)).toENNReal = ENNReal.ofReal (-L y) := fun y => by
    rw [← EReal.coe_neg, EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
  unfold extIntegral
  simp only [h1, h2]
  have hp : ∫⁻ y, ENNReal.ofReal (L y) ∂μ ≠ ⊤ := hLi.lintegral_lt_top.ne
  have hn : ∫⁻ y, ENNReal.ofReal (-L y) ∂μ ≠ ⊤ := hLi.neg.lintegral_lt_top.ne
  rw [← EReal.coe_ennreal_toReal hp, ← EReal.coe_ennreal_toReal hn, ← EReal.coe_sub,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hLi]

/-- The extended integral of a real function bounded above by `s + l c`. -/
lemma extIntegral_le {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsProbabilityMeasure μ]
    (L c : Y → ℝ) (hL : Measurable L) (hc : Measurable c) (hc0 : ∀ y, 0 ≤ c y)
    (s l a : ℝ) (hl : 0 ≤ l) (ha : 0 ≤ a) (hb : ∀ y, L y ≤ s + l * c y)
    (hca : ∫⁻ y, ENNReal.ofReal (c y) ∂μ ≤ ENNReal.ofReal a) :
    extIntegral μ (fun y => (L y : EReal)) ≤ ((s + l * a : ℝ) : EReal) := by
  have hci : Integrable c μ := by
    refine ⟨hc.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hc0)]
    exact lt_of_le_of_lt hca ENNReal.ofReal_lt_top
  by_cases hneg : ∫⁻ y, ENNReal.ofReal (-L y) ∂μ = ⊤
  · have h2 : ∀ y, (-(L y : EReal)).toENNReal = ENNReal.ofReal (-L y) := fun y => by
      rw [← EReal.coe_neg, EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
    unfold extIntegral
    simp only [h2, hneg, EReal.coe_ennreal_top, EReal.sub_top]
    exact bot_le
  · have hg : Integrable (fun y => |s| + l * c y) μ := (integrable_const _).add (hci.const_mul l)
    have hpos : Integrable (fun y => max (L y) 0) μ := by
      refine Integrable.mono' hg (hL.max measurable_const).aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      refine max_le ?_ ?_
      · have := hb y; have := le_abs_self s; linarith
      · have := hc0 y; positivity
    have hnegi : Integrable (fun y => max (-L y) 0) μ := by
      refine ⟨(hL.neg.max measurable_const).aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal (f := fun y => max (-L y) 0)
        (Filter.Eventually.of_forall fun y => le_max_right _ _)]
      have : ∀ y, ENNReal.ofReal (max (-L y) 0) = ENNReal.ofReal (-L y) := fun y => by
        rcases le_total 0 (-L y) with h | h
        · rw [max_eq_left h]
        · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
      simp_rw [this]; exact lt_top_iff_ne_top.2 hneg
    have hLi : Integrable L μ := by
      have : L = fun y => max (L y) 0 - max (-L y) 0 := by
        funext y; rcases le_total 0 (L y) with h | h
        · rw [max_eq_left h, max_eq_right (neg_nonpos.2 h)]; ring
        · rw [max_eq_right h, max_eq_left (neg_nonneg.2 h)]; ring
      rw [this]; exact hpos.sub hnegi
    rw [extIntegral_eq_integral μ L hLi, EReal.coe_le_coe_iff]
    have hint : ∫ y, L y ∂μ ≤ ∫ y, (s + l * c y) ∂μ :=
      integral_mono hLi ((integrable_const _).add (hci.const_mul l)) hb
    rw [integral_add (integrable_const _) (hci.const_mul l), integral_const, integral_const_mul]
      at hint
    have hc_le : ∫ y, c y ∂μ ≤ a := by
      rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hc0)
        hc.aestronglyMeasurable]
      exact ENNReal.toReal_le_of_le_ofReal ha hca
    simp only [probReal_univ, one_smul] at hint
    nlinarith

end CondPortOTConicAux

open CondPortOTConicAux in
theorem solution {Y : Type*} [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] (DY : Y → Y → ℝ) (hDYnn : ∀ y y', 0 ≤ DY y y')
    (hDYc : Continuous (fun p : Y × Y => DY p.1 p.2)) (hDY0 : ∀ y, DY y y = 0)
    (yhat : Y) (L : Y → ℝ) (hL : Measurable L) (υ θ : ℝ) (hυ : 0 ≤ υ) (hθ : 0 < θ) :
    (⨆ (μ : Measure Y) (_ : IsProbabilityMeasure μ ∧
        ENNReal.ofReal υ * ∫⁻ y, ENNReal.ofReal (DY y yhat) ∂μ ≤ ENNReal.ofReal θ),
      ((υ : ℝ) : EReal) * extIntegral μ (fun y => (L y : EReal))) =
    ⨅ (l : ℝ) (_ : 0 ≤ l),
      ((θ * l : ℝ) : EReal) + ((υ : ℝ) : EReal) * ⨆ y, ((L y - l * DY y yhat : ℝ) : EReal) := by
  set c : Y → ℝ := fun y => DY y yhat with hc_def
  have hcm : Measurable c :=
    (hDYc.comp (continuous_id.prodMk continuous_const)).measurable
  rcases hυ.eq_or_lt with h0 | hpos
  · subst h0
    simp only [EReal.coe_zero, zero_mul, add_zero]
    apply le_antisymm
    · refine iSup₂_le fun _ _ => ?_
      exact le_iInf₂ fun l hl => by exact_mod_cast mul_nonneg hθ.le hl
    · refine le_trans (iInf₂_le 0 le_rfl) ?_
      refine le_trans ?_ (le_iSup₂ (f := fun (μ : Measure Y) (_ : IsProbabilityMeasure μ ∧
        ENNReal.ofReal 0 * ∫⁻ y, ENNReal.ofReal (DY y yhat) ∂μ ≤ ENNReal.ofReal θ) => (0 : EReal))
        (Measure.dirac yhat) ⟨inferInstance, by simp⟩)
      simp
  apply le_antisymm
  · refine iSup₂_le fun μ hμ => le_iInf₂ fun l hl => ?_
    obtain ⟨hprob, hcost⟩ := hμ
    by_cases hS : (⨆ y, ((L y - l * DY y yhat : ℝ) : EReal)) = ⊤
    · rw [hS, EReal.coe_mul_top_of_pos hpos, EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)]
      exact le_top
    · set S := ⨆ y, ((L y - l * DY y yhat : ℝ) : EReal) with hSdef
      have hSbot : S ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot (L yhat - l * DY yhat yhat))
        (le_iSup (fun y => ((L y - l * DY y yhat : ℝ) : EReal)) yhat)
      set s := S.toReal
      have hSs : S = (s : EReal) := (EReal.coe_toReal hS hSbot).symm
      have hb : ∀ y, L y ≤ s + l * c y := fun y => by
        have : ((L y - l * DY y yhat : ℝ) : EReal) ≤ S :=
          le_iSup (fun y => ((L y - l * DY y yhat : ℝ) : EReal)) y
        rw [hSs, EReal.coe_le_coe_iff] at this
        simp only [hc_def]; linarith
      have hca : ∫⁻ y, ENNReal.ofReal (c y) ∂μ ≤ ENNReal.ofReal (θ / υ) := by
        rw [ENNReal.ofReal_div_of_pos hpos,
          ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hpos))
            (Or.inl ENNReal.ofReal_ne_top), mul_comm]
        exact hcost
      have hle := extIntegral_le μ L c hL hcm (fun y => hDYnn _ _) s l (θ / υ) hl
        (div_nonneg hθ.le hpos.le) hb hca
      rw [hSs]
      calc ((υ : ℝ) : EReal) * extIntegral μ (fun y => (L y : EReal))
          ≤ ((υ : ℝ) : EReal) * ((s + l * (θ / υ) : ℝ) : EReal) :=
            mul_le_mul_of_nonneg_left hle (by exact_mod_cast hpos.le)
        _ = ((θ * l : ℝ) : EReal) + ((υ : ℝ) : EReal) * (s : EReal) := by
            rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
            congr 1
            field_simp
            ring
  · rw [← EReal.le_of_forall_lt_iff_le]
    intro M hM
    set a : ℝ := θ / υ with ha_def
    set m : ℝ := M / υ with hm_def
    have hapos : 0 < a := div_pos hθ hpos
    set C : Set (ℝ × ℝ) := Set.range (fun y => (c y, L y)) with hC_def
    set Qd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Iio 0 with hQd_def
    set K : Set (ℝ × ℝ) := convexHull ℝ C + Qd with hK_def
    have hKconv : Convex ℝ K := (convex_convexHull ℝ C).add ((convex_Ioi 0).prod (convex_Iio 0))
    have hKopen : IsOpen K := IsOpen.add_left (isOpen_Ioi.prod isOpen_Iio)
    have hnot : (a, m) ∉ K := by
      intro hmem
      obtain ⟨z, hz, q, hq, hzq⟩ := Set.mem_add.1 hmem
      rw [convexHull_eq] at hz
      obtain ⟨ι, t, w, zz, hw0, hw1, hzz, hcmz⟩ := hz
      have hex : ∀ i ∈ t, ∃ y, (c y, L y) = zz i := fun i hi => hzz i hi
      have : Nonempty Y := ⟨yhat⟩
      choose! yy hyy using hex
      let μ : Measure Y := ∑ i ∈ t, ENNReal.ofReal (w i) • Measure.dirac (yy i)
      have hz_eq : z = ∑ i ∈ t, w i • zz i := by
        rw [← hcmz, Finset.centerMass_eq_of_sum_1 _ _ hw1]
      have hz1 : z.1 = ∑ i ∈ t, w i * c (yy i) := by
        rw [hz_eq, Prod.fst_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Prod.smul_fst, smul_eq_mul, ← hyy i hi]
      have hz2 : z.2 = ∑ i ∈ t, w i * L (yy i) := by
        rw [hz_eq, Prod.snd_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Prod.smul_snd, smul_eq_mul, ← hyy i hi]
      have hq1 : 0 < q.1 := hq.1
      have hq2 : q.2 < 0 := hq.2
      have hzq1 : z.1 + q.1 = a := by rw [← Prod.fst_add, hzq]
      have hzq2 : z.2 + q.2 = m := by rw [← Prod.snd_add, hzq]
      have hμprob : IsProbabilityMeasure μ := by
        constructor
        simp only [μ, Measure.coe_finset_sum, Finset.sum_apply, Measure.smul_apply,
          measure_univ, smul_eq_mul, mul_one]
        rw [← ENNReal.ofReal_sum_of_nonneg hw0, hw1, ENNReal.ofReal_one]
      have hlint : ∀ g : Y → ENNReal,
          ∫⁻ y, g y ∂μ = ∑ i ∈ t, ENNReal.ofReal (w i) * g (yy i) := by
        intro g
        simp only [μ, lintegral_finset_sum_measure, lintegral_smul_measure, lintegral_dirac,
          smul_eq_mul]
      have hLint : Integrable L μ := by
        refine integrable_finsetSum_measure.2 fun i _ => ?_
        exact (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top
      have hintL : ∫ y, L y ∂μ = ∑ i ∈ t, w i * L (yy i) := by
        simp only [μ]
        rw [integral_finsetSum_measure fun i _ =>
          (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hw0 i hi),
          smul_eq_mul]
      have hfeas : ENNReal.ofReal υ * ∫⁻ y, ENNReal.ofReal (DY y yhat) ∂μ ≤ ENNReal.ofReal θ := by
        have : ∫⁻ y, ENNReal.ofReal (DY y yhat) ∂μ = ENNReal.ofReal z.1 := by
          rw [hlint, hz1, ENNReal.ofReal_sum_of_nonneg fun i hi =>
            mul_nonneg (hw0 i hi) (hDYnn _ _)]
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [ENNReal.ofReal_mul (hw0 i hi)]
        rw [this, ← ENNReal.ofReal_mul hpos.le]
        apply ENNReal.ofReal_le_ofReal
        have : υ * a = θ := by rw [ha_def]; field_simp
        nlinarith
      have hterm : ((υ : ℝ) : EReal) * extIntegral μ (fun y => (L y : EReal)) ≤
          ⨆ (μ : Measure Y) (_ : IsProbabilityMeasure μ ∧
            ENNReal.ofReal υ * ∫⁻ y, ENNReal.ofReal (DY y yhat) ∂μ ≤ ENNReal.ofReal θ),
            ((υ : ℝ) : EReal) * extIntegral μ (fun y => (L y : EReal)) :=
        le_iSup₂ (f := fun (μ : Measure Y) (_ : IsProbabilityMeasure μ ∧
            ENNReal.ofReal υ * ∫⁻ y, ENNReal.ofReal (DY y yhat) ∂μ ≤ ENNReal.ofReal θ) =>
            ((υ : ℝ) : EReal) * extIntegral μ (fun y => (L y : EReal))) μ ⟨hμprob, hfeas⟩
      rw [extIntegral_eq_integral μ L hLint, hintL, ← EReal.coe_mul] at hterm
      have hgt : M < υ * ∑ i ∈ t, w i * L (yy i) := by
        rw [← hz2]
        have : υ * m = M := by rw [hm_def]; field_simp
        nlinarith
      have := lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 hgt) hterm
      exact absurd hM (not_lt.2 this.le)
    obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hKconv hKopen hnot
    have hf_apply : ∀ u w : ℝ, f (u, w) = u * f (1, 0) + w * f (0, 1) := by
      intro u w
      have : ((u, w) : ℝ × ℝ) = u • ((1 : ℝ), (0 : ℝ)) + w • ((0 : ℝ), (1 : ℝ)) := by
        ext <;> simp
      rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    set p := f (1, 0) with hp_def
    set q := f (0, 1) with hq_def
    have hmemK : ∀ y (r r' : ℝ), 0 < r → 0 < r' → (c y + r, L y - r') ∈ K := by
      intro y r r' hr hr'
      refine Set.mem_add.2 ⟨(c y, L y), subset_convexHull ℝ C ⟨y, rfl⟩, (r, -r'),
        ⟨hr, by simp [hr']⟩, ?_⟩
      simp [sub_eq_add_neg]
    have hK' : ∀ y (r r' : ℝ), 0 < r → 0 < r' →
        (c y + r) * p + (L y - r') * q < a * p + m * q := by
      intro y r r' hr hr'
      have := hf _ (hmemK y r r' hr hr')
      rwa [hf_apply, hf_apply] at this
    have hc0 : c yhat = 0 := hDY0 yhat
    have hqpos : 0 < q := by
      by_contra hq
      push Not at hq
      have h := hK' yhat a (|L yhat - m| + 1) hapos (by positivity)
      rw [hc0] at h
      have h1 : L yhat - m ≤ |L yhat - m| := le_abs_self _
      nlinarith
    have hpneg : p ≤ 0 := by
      by_contra hp
      push Not at hp
      set X := (m - (L yhat - 1)) * q
      have h := hK' yhat ((|X| + 1) / p + a) 1 (by positivity) one_pos
      rw [hc0, zero_add, add_mul, div_mul_cancel₀ _ hp.ne'] at h
      have : X ≤ |X| := le_abs_self X
      simp only [X] at this
      nlinarith
    have hkey : ∀ y, c y * p + L y * q ≤ a * p + m * q := by
      intro y
      refine le_of_forall_pos_lt_add fun ε hε => ?_
      have hqp : 0 < q - p := by linarith
      have h := hK' y (ε / (q - p)) (ε / (q - p)) (div_pos hε hqp) (div_pos hε hqp)
      have he : ε / (q - p) * (q - p) = ε := div_mul_cancel₀ _ hqp.ne'
      nlinarith
    set l : ℝ := -p / q with hl_def
    have hl0 : 0 ≤ l := div_nonneg (neg_nonneg.2 hpneg) hqpos.le
    have hbound : ∀ y, L y - l * DY y yhat ≤ m - l * a := by
      intro y
      have h := hkey y
      have e1 : L y - l * DY y yhat = (c y * p + L y * q) / q := by
        rw [hl_def, hc_def]; field_simp; ring
      have e2 : m - l * a = (a * p + m * q) / q := by
        rw [hl_def]; field_simp; ring
      rw [e1, e2]
      exact div_le_div_of_nonneg_right h hqpos.le
    calc (⨅ (l : ℝ) (_ : 0 ≤ l),
          ((θ * l : ℝ) : EReal) + ((υ : ℝ) : EReal) * ⨆ y, ((L y - l * DY y yhat : ℝ) : EReal))
        ≤ ((θ * l : ℝ) : EReal) + ((υ : ℝ) : EReal) * ⨆ y, ((L y - l * DY y yhat : ℝ) : EReal) :=
          iInf₂_le l hl0
      _ ≤ ((θ * l : ℝ) : EReal) + ((υ : ℝ) : EReal) * ((m - l * a : ℝ) : EReal) := by
          exact add_le_add_right (mul_le_mul_of_nonneg_left
            (iSup_le fun y => EReal.coe_le_coe_iff.2 (hbound y)) (by exact_mod_cast hpos.le)) _
      _ = (M : EReal) := by
          rw [← EReal.coe_mul, ← EReal.coe_add, EReal.coe_eq_coe_iff, hm_def, ha_def]
          field_simp
          ring
