-- Prove2me | solution 1 for FiniteEnergyPlane.ofReal_integral_le_lintegral_of_injOn_sweep
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-26T21:33:25.833739+00:00
-- url     : https://prove2.me/submissions/4b78ce4b-99d5-466f-8bcd-a54da2816f3b

import Mathlib



/-! Child A of P c5a21fab: `ofReal_integral_le_lintegral_of_injOn_sweep`. -/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal

theorem olpa_det (L : ℂ →L[ℝ] ℂ) :
    L.det = (L 1).re * (L Complex.I).im - (L 1).im * (L Complex.I).re := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI_repr, Complex.coe_basisOneI]
  ring

theorem olpa_ofReal_integral_le {μ : Measure ℝ} {u : ℝ → ℝ} (hu : Integrable u μ) :
    ENNReal.ofReal (∫ x, u x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (u x) ∂μ := by
  have h1 : ∫ x, u x ∂μ ≤ ∫ x, max (u x) 0 ∂μ :=
    integral_mono hu (hu.sup (integrable_zero _ _ _)) fun x => le_max_left _ _
  have h2 : ENNReal.ofReal (∫ x, max (u x) 0 ∂μ) = ∫⁻ x, ENNReal.ofReal (max (u x) 0) ∂μ :=
    ofReal_integral_eq_lintegral_ofReal (hu.sup (integrable_zero _ _ _))
      (Eventually.of_forall fun x => le_max_right _ _)
  calc ENNReal.ofReal (∫ x, u x ∂μ) ≤ ENNReal.ofReal (∫ x, max (u x) 0 ∂μ) :=
        ENNReal.ofReal_le_ofReal h1
    _ = ∫⁻ x, ENNReal.ofReal (u x) ∂μ := by
        rw [h2]; congr 1; funext x
        rcases le_total (u x) 0 with h | h
        · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
        · rw [max_eq_left h]

theorem olpa_ofReal_intervalIntegral_le {u : ℝ → ℝ} (hu : Continuous u) {a b : ℝ} (hab : a ≤ b) :
    ENNReal.ofReal (∫ x in a..b, u x) ≤ ∫⁻ x in Ioo a b, ENNReal.ofReal (u x) := by
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
  exact olpa_ofReal_integral_le ((hu.integrableOn_Icc).mono_set Ioo_subset_Icc_self)

/-- Tonelli on the plane, in the coordinates `p = τ + t i`, outer variable `t`. -/
theorem olpa_lintegral_strip (g : ℂ → ℝ≥0∞) (hg : Measurable g) (A B : Set ℝ)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∫⁻ p in {p : ℂ | p.re ∈ A ∧ p.im ∈ B}, g p =
      ∫⁻ t in B, ∫⁻ τ in A, g (τ + t * Complex.I) := by
  have hmp := Complex.volume_preserving_equiv_real_prod
  have hS : {p : ℂ | p.re ∈ A ∧ p.im ∈ B} = Complex.measurableEquivRealProd ⁻¹' (A ×ˢ B) := by
    ext p; simp [Complex.measurableEquivRealProd]
  have hg' : ∀ p, g p = (g ∘ Complex.measurableEquivRealProd.symm)
      (Complex.measurableEquivRealProd p) := fun p => by simp
  simp_rw [hS, hg']
  rw [hmp.setLIntegral_comp_preimage_emb Complex.measurableEquivRealProd.measurableEmbedding,
    Measure.volume_eq_prod, ← Measure.prod_restrict]
  have hm : Measurable (g ∘ Complex.measurableEquivRealProd.symm) :=
    hg.comp Complex.measurableEquivRealProd.symm.measurable
  rw [lintegral_prod_symm _ hm.aemeasurable]
  refine lintegral_congr fun t => lintegral_congr fun τ => ?_
  simp only [Function.comp_apply, Complex.measurableEquivRealProd_symm_apply]
  congr 1
  apply Complex.ext <;> simp

/-- Swapped Tonelli, outer variable `τ`. -/
theorem olpa_lintegral_strip' (g : ℂ → ℝ≥0∞) (hg : Measurable g) (A B : Set ℝ)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∫⁻ p in {p : ℂ | p.re ∈ A ∧ p.im ∈ B}, g p =
      ∫⁻ τ in A, ∫⁻ t in B, g (τ + t * Complex.I) := by
  rw [olpa_lintegral_strip g hg A B hA hB]
  have hm : Measurable (fun q : ℝ × ℝ => g (q.2 + q.1 * Complex.I)) :=
    hg.comp ((Complex.measurable_ofReal.comp measurable_snd).add
      ((Complex.measurable_ofReal.comp measurable_fst).mul measurable_const))
  exact lintegral_lintegral_swap hm.aemeasurable

/-- Positivity propagates along `u' = a u`. -/
theorem olpa_pos_of_hasDerivAt {u a : ℝ → ℝ} (ha : Continuous a)
    (hu : ∀ τ ≤ 0, HasDerivAt u (a τ * u τ) τ) (h0 : 0 < u 0) : ∀ τ ≤ 0, 0 < u τ := by
  intro τ₁ hτ₁
  set E : ℝ → ℝ := fun τ => ∫ s in (0 : ℝ)..τ, a s with hE
  have hEd : ∀ τ, HasDerivAt E (a τ) τ := fun τ =>
    (ha.integral_hasStrictDerivAt 0 τ).hasDerivAt
  set φ : ℝ → ℝ := fun τ => u τ * Real.exp (-E τ) with hφ
  have hφd : ∀ τ ≤ 0, HasDerivAt φ 0 τ := by
    intro τ hτ
    have := (hu τ hτ).mul ((hEd τ).neg.exp)
    refine this.congr_deriv ?_
    ring
  have hc : ContinuousOn φ (Icc τ₁ 0) := fun τ hτ =>
    (hφd τ hτ.2).continuousAt.continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero hc
    (fun τ hτ => (hφd τ hτ.2.le).hasDerivWithinAt) 0 ⟨hτ₁, le_rfl⟩
  have hE0 : E 0 = 0 := by simp [hE]
  have hφ0 : φ 0 = u 0 := by simp [hφ, hE0]
  have : 0 < φ τ₁ := by rw [← hconst, hφ0]; exact h0
  have hpos := this
  simp only [hφ] at hpos
  exact pos_of_mul_pos_left hpos (Real.exp_pos _).le

theorem ofReal_integral_le_lintegral_of_injOn_sweep_aux (G : ℂ → ℂ) (G' : ℂ → ℂ →L[ℝ] ℂ)
    (hG : ∀ p, HasFDerivAt G (G' p) p) (J : ℂ → ℝ)
    (hJ : ∀ p, J p = (G' p 1).re * (G' p Complex.I).im - (G' p 1).im * (G' p Complex.I).re)
    (hJc : Continuous J) (f : ℂ → ℝ) (hf : Continuous f)
    (hJd : ∀ p : ℂ, p.re ≤ 0 → p.im ∈ Icc (0 : ℝ) 1 →
      HasDerivAt (fun τ : ℝ => J (τ + p.im * Complex.I)) (f (G p) * J p) p.re)
    (hJ0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 < J (t * Complex.I))
    (hinj : InjOn G {p : ℂ | p.re < 0 ∧ p.im ∈ Ico (0 : ℝ) 1})
    (hmaps : MapsTo G {p : ℂ | p.re < 0 ∧ p.im ∈ Ico (0 : ℝ) 1} (ball 0 1)) :
    ENNReal.ofReal (∫ t in (0 : ℝ)..1, J (t * Complex.I)) ≤
      ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (f z) := by
  set Q : Set ℂ := {p : ℂ | p.re < 0 ∧ p.im ∈ Ico (0 : ℝ) 1} with hQ
  have hGc : Continuous G := continuous_iff_continuousAt.2 fun p => (hG p).continuousAt
  have hpt : ∀ (τ t : ℝ), ((τ : ℂ) + t * Complex.I).re = τ ∧ ((τ : ℂ) + t * Complex.I).im = t :=
    fun τ t => ⟨by simp, by simp⟩
  have hlin : Continuous (fun q : ℝ × ℝ => ((q.1 : ℂ) + q.2 * Complex.I)) :=
    (Complex.continuous_ofReal.comp continuous_fst).add
      ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
  -- derivative along the strip, in coordinates
  have hJd' : ∀ t ∈ Icc (0 : ℝ) 1, ∀ τ : ℝ, τ ≤ 0 → HasDerivAt (fun τ' : ℝ => J (τ' + t * Complex.I))
      (f (G (τ + t * Complex.I)) * J (τ + t * Complex.I)) τ := by
    intro t ht τ hτ
    have h := hJd (τ + t * Complex.I) (by rw [(hpt τ t).1]; exact hτ) (by rw [(hpt τ t).2]; exact ht)
    rw [(hpt τ t).1, (hpt τ t).2] at h
    exact h
  -- positivity of the Jacobian on the closed half-strip
  have hJpos : ∀ t ∈ Icc (0 : ℝ) 1, ∀ τ : ℝ, τ ≤ 0 → 0 < J (τ + t * Complex.I) := by
    intro t ht
    have ha : Continuous (fun τ : ℝ => f (G (τ + t * Complex.I))) :=
      hf.comp (hGc.comp (hlin.comp (continuous_id.prodMk continuous_const)))
    refine olpa_pos_of_hasDerivAt ha (fun τ hτ => hJd' t ht τ hτ) ?_
    simpa using hJ0 t ht
  -- change of variables
  have hdet : ∀ p, (G' p).det = J p := fun p => by rw [olpa_det, hJ]
  have hQm : MeasurableSet Q :=
    (measurableSet_lt Complex.measurable_re measurable_const).inter
      (Complex.measurable_im measurableSet_Ico)
  have hcov : ∀ S ⊆ Q, MeasurableSet S → ∀ φ : ℂ → ℝ≥0∞,
      ∫⁻ x in G '' S, φ x = ∫⁻ x in S, ENNReal.ofReal |J x| * φ (G x) := by
    intro S hSQ hS φ
    rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS
      (fun x _ => (hG x).hasFDerivWithinAt) (hinj.mono hSQ) φ]
    simp_rw [hdet]
  -- finiteness of the swept area
  have hfin : ∫⁻ x in Q, ENNReal.ofReal |J x| < ∞ := by
    have h := hcov Q le_rfl hQm (fun _ => 1)
    simp only [mul_one, setLIntegral_one] at h
    rw [← h]
    exact lt_of_le_of_lt (measure_mono hmaps.image_subset) measure_ball_lt_top
  have hJm : Measurable (fun x => ENNReal.ofReal |J x|) :=
    ENNReal.measurable_ofReal.comp (hJc.abs.measurable)
  set k : ℝ → ℝ≥0∞ := fun τ => ∫⁻ t in Ico (0 : ℝ) 1, ENNReal.ofReal |J (τ + t * Complex.I)| with hk
  have hQk : ∫⁻ x in Q, ENNReal.ofReal |J x| = ∫⁻ τ in Iio (0 : ℝ), k τ := by
    have := olpa_lintegral_strip' (fun x => ENNReal.ofReal |J x|) hJm (Iio 0) (Ico 0 1)
      measurableSet_Iio measurableSet_Ico
    exact this
  have hsmall : ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ τ < (0 : ℝ), k τ < ε := by
    intro ε hε
    by_contra hcon
    push_neg at hcon
    have h1 : ∫⁻ τ in Iio (0 : ℝ), ε ≤ ∫⁻ τ in Iio (0 : ℝ), k τ :=
      setLIntegral_mono' measurableSet_Iio hcon
    rw [setLIntegral_const, Real.volume_Iio, ENNReal.mul_top hε, ← hQk] at h1
    exact absurd (lt_of_le_of_lt h1 hfin) (lt_irrefl _)
  -- the main estimate
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨τ₁, hτ₁, hkτ⟩ := hsmall ε (by exact_mod_cast hε.ne')
  set S : Set ℂ := {p : ℂ | p.re ∈ Ioo τ₁ 0 ∧ p.im ∈ Ioo (0 : ℝ) 1} with hSdef
  have hSQ : S ⊆ Q := fun p hp => ⟨hp.1.2, Ioo_subset_Ico_self hp.2⟩
  have hSm : MeasurableSet S :=
    (Complex.measurable_re measurableSet_Ioo).inter (Complex.measurable_im measurableSet_Ioo)
  -- FTC in τ
  have hftc : ∀ t ∈ Icc (0 : ℝ) 1, J (t * Complex.I) - J (τ₁ + t * Complex.I) =
      ∫ τ in τ₁..0, f (G (τ + t * Complex.I)) * J (τ + t * Complex.I) := by
    intro t ht
    have hc : Continuous (fun τ : ℝ => f (G (τ + t * Complex.I)) * J (τ + t * Complex.I)) :=
      (hf.comp (hGc.comp (hlin.comp (continuous_id.prodMk continuous_const)))).mul
        (hJc.comp (hlin.comp (continuous_id.prodMk continuous_const)))
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun τ' : ℝ => J (τ' + t * Complex.I))
      (fun τ hτ => hJd' t ht τ (by
        rw [uIcc_of_le hτ₁.le] at hτ; exact hτ.2)) (hc.intervalIntegrable _ _)]
    simp
  have hcont0 : Continuous (fun t : ℝ => J (t * Complex.I)) :=
    hJc.comp (Complex.continuous_ofReal.mul continuous_const)
  have hcont1 : Continuous (fun t : ℝ => J (τ₁ + t * Complex.I)) :=
    hJc.comp (hlin.comp (continuous_const.prodMk continuous_id))
  have hsplit : ∫ t in (0 : ℝ)..1, J (t * Complex.I) =
      (∫ t in (0 : ℝ)..1, J (τ₁ + t * Complex.I)) +
        ∫ t in (0 : ℝ)..1, (J (t * Complex.I) - J (τ₁ + t * Complex.I)) := by
    rw [intervalIntegral.integral_sub (hcont0.intervalIntegrable _ _) (hcont1.intervalIntegrable _ _)]
    ring
  -- the tail
  have htail : ENNReal.ofReal (∫ t in (0 : ℝ)..1, J (τ₁ + t * Complex.I)) ≤ k τ₁ := by
    calc ENNReal.ofReal (∫ t in (0 : ℝ)..1, J (τ₁ + t * Complex.I))
        ≤ ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (J (τ₁ + t * Complex.I)) :=
          olpa_ofReal_intervalIntegral_le hcont1 zero_le_one
      _ ≤ ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal |J (τ₁ + t * Complex.I)| :=
          lintegral_mono fun t => ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ ≤ k τ₁ := lintegral_mono_set Ioo_subset_Ico_self
  -- the swept part
  have hswept : ENNReal.ofReal (∫ t in (0 : ℝ)..1, (J (t * Complex.I) - J (τ₁ + t * Complex.I))) ≤
      ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (f z) := by
    have hfm : Measurable (fun x => ENNReal.ofReal |J x| * ENNReal.ofReal (f (G x))) :=
      hJm.mul (ENNReal.measurable_ofReal.comp (hf.comp hGc).measurable)
    calc ENNReal.ofReal (∫ t in (0 : ℝ)..1, (J (t * Complex.I) - J (τ₁ + t * Complex.I)))
        ≤ ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (J (t * Complex.I) - J (τ₁ + t * Complex.I)) :=
          olpa_ofReal_intervalIntegral_le (hcont0.sub hcont1) zero_le_one
      _ ≤ ∫⁻ t in Ioo (0 : ℝ) 1, ∫⁻ τ in Ioo τ₁ 0,
            ENNReal.ofReal |J (τ + t * Complex.I)| * ENNReal.ofReal (f (G (τ + t * Complex.I))) := by
          refine setLIntegral_mono' measurableSet_Ioo fun t ht => ?_
          have ht' : t ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht
          rw [hftc t ht']
          have hc : Continuous (fun τ : ℝ => f (G (τ + t * Complex.I)) * J (τ + t * Complex.I)) :=
            (hf.comp (hGc.comp (hlin.comp (continuous_id.prodMk continuous_const)))).mul
              (hJc.comp (hlin.comp (continuous_id.prodMk continuous_const)))
          refine (olpa_ofReal_intervalIntegral_le hc hτ₁.le).trans
            (setLIntegral_mono' measurableSet_Ioo fun τ hτ => ?_)
          have hJp := hJpos t ht' τ hτ.2.le
          rw [abs_of_pos hJp, ENNReal.ofReal_mul' hJp.le, mul_comm]
      _ = ∫⁻ x in S, ENNReal.ofReal |J x| * ENNReal.ofReal (f (G x)) :=
          (olpa_lintegral_strip _ hfm (Ioo τ₁ 0) (Ioo 0 1) measurableSet_Ioo measurableSet_Ioo).symm
      _ = ∫⁻ z in G '' S, ENNReal.ofReal (f z) := (hcov S hSQ hSm (fun z => ENNReal.ofReal (f z))).symm
      _ ≤ ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (f z) :=
          lintegral_mono_set ((Set.image_mono hSQ).trans hmaps.image_subset)
  rw [hsplit]
  calc ENNReal.ofReal ((∫ t in (0 : ℝ)..1, J (τ₁ + t * Complex.I)) +
        ∫ t in (0 : ℝ)..1, (J (t * Complex.I) - J (τ₁ + t * Complex.I)))
      ≤ ENNReal.ofReal (∫ t in (0 : ℝ)..1, J (τ₁ + t * Complex.I)) +
        ENNReal.ofReal (∫ t in (0 : ℝ)..1, (J (t * Complex.I) - J (τ₁ + t * Complex.I))) :=
        ENNReal.ofReal_add_le
    _ ≤ k τ₁ + ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (f z) := add_le_add htail hswept
    _ ≤ (∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (f z)) + ε := by
        rw [add_comm]; exact add_le_add le_rfl hkτ.le

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Set
open scoped ENNReal

theorem solution (G : ℂ → ℂ) (G' : ℂ → ℂ →L[ℝ] ℂ)
    (hG : ∀ p, HasFDerivAt G (G' p) p) (J : ℂ → ℝ)
    (hJ : ∀ p, J p = (G' p 1).re * (G' p Complex.I).im - (G' p 1).im * (G' p Complex.I).re)
    (hJc : Continuous J) (f : ℂ → ℝ) (hf : Continuous f)
    (hJd : ∀ p : ℂ, p.re ≤ 0 → p.im ∈ Icc (0 : ℝ) 1 →
      HasDerivAt (fun τ : ℝ => J (τ + p.im * Complex.I)) (f (G p) * J p) p.re)
    (hJ0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 < J (t * Complex.I))
    (hinj : InjOn G {p : ℂ | p.re < 0 ∧ p.im ∈ Ico (0 : ℝ) 1})
    (hmaps : MapsTo G {p : ℂ | p.re < 0 ∧ p.im ∈ Ico (0 : ℝ) 1} (ball 0 1)) :
    ENNReal.ofReal (∫ t in (0 : ℝ)..1, J (t * Complex.I)) ≤
      ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (f z) :=
  ofReal_integral_le_lintegral_of_injOn_sweep_aux G G' hG J hJ hJc f hf hJd hJ0 hinj hmaps
