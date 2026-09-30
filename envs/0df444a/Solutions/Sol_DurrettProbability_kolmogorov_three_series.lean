-- Prove2me | solution 1 for DurrettProbability.kolmogorov_three_series
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-28T00:15:20.43799+00:00
-- url     : https://prove2.me/submissions/900f0f82-740e-4f1a-afe5-c44476af7bcb

import Mathlib
import Definitions.Def_DurrettProbability_Series

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter DurrettProbability in
lemma p2m40_sum_congr_tail (a b : ℕ → ℝ) (n0 : ℕ) (h : ∀ n ≥ n0, a n = b n) (L : ℝ)
    (hb : Tendsto (fun N => ∑ n ∈ Finset.range N, b n) atTop (nhds L)) :
    ∃ L' : ℝ, Tendsto (fun N => ∑ n ∈ Finset.range N, a n) atTop (nhds L') := by
  refine ⟨L + (∑ n ∈ Finset.range n0, a n - ∑ n ∈ Finset.range n0, b n), ?_⟩
  refine (hb.add tendsto_const_nhds).congr' ?_
  filter_upwards [eventually_ge_atTop n0] with N hN
  have h1 : ∑ n ∈ Finset.range N, (a n - b n) = ∑ n ∈ Finset.range n0, (a n - b n) := by
    rw [← Finset.sum_range_add_sum_Ico _ hN, Finset.sum_eq_zero (s := Finset.Ico n0 N)
      (fun n hn => by rw [h n (Finset.mem_Ico.1 hn).1, sub_self]), add_zero]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at h1
  linarith

open MeasureTheory ProbabilityTheory Filter DurrettProbability in
lemma p2m40_int_bdd {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (F : Ω → ℝ) (hF : Measurable F) (B : ℝ) (hB : ∀ x, |F x| ≤ B) : Integrable F μ :=
  Integrable.of_bound hF.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hB x)

open MeasureTheory ProbabilityTheory Filter DurrettProbability in
/-- L² martingale convergence: centred independent summands with summable variances. -/
lemma p2m40_centered {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (Z : ℕ → Ω → ℝ) (hmeas : ∀ i, Measurable (Z i))
    (hindep : iIndepFun Z μ) (hL2 : ∀ i, MemLp (Z i) 2 μ) (hmean : ∀ i, μ[Z i] = 0)
    (hvar : Summable (fun n => Var[Z n; μ])) :
    ∀ᵐ ω ∂μ, ∃ L : ℝ, Tendsto (fun N => ∑ n ∈ Finset.range N, Z n ω) atTop (nhds L) := by
  have hsm : ∀ i, StronglyMeasurable (Z i) := fun i => (hmeas i).stronglyMeasurable
  let ℱ : Filtration ℕ ‹MeasurableSpace Ω› := Filtration.natural Z hsm
  let f : ℕ → Ω → ℝ := fun n ω => ∑ k ∈ Finset.range (n + 1), Z k ω
  have hZℱ : ∀ k n, k ≤ n → StronglyMeasurable[ℱ n] (Z k) := by
    intro k n hkn
    have h1 : Measurable[MeasurableSpace.comap (Z k) inferInstance] (Z k) :=
      comap_measurable (Z k)
    have h2 : MeasurableSpace.comap (Z k) inferInstance ≤ ℱ n := by
      show MeasurableSpace.comap (Z k) _ ≤ ⨆ j ≤ n, MeasurableSpace.comap (Z j) _
      exact le_iSup₂ (f := fun j (_ : j ≤ n) => MeasurableSpace.comap (Z j) inferInstance) k hkn
    exact (h1.mono h2 le_rfl).stronglyMeasurable
  have hadapt : StronglyAdapted ℱ f := by
    intro n
    refine Finset.stronglyMeasurable_fun_sum _ (fun k hk => hZℱ k n ?_)
    exact Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  have hint : ∀ i, Integrable (f i) μ := fun i =>
    integrable_finsetSum _ (fun k _ => (hL2 k).integrable one_le_two)
  have hmart : Martingale f ℱ μ := by
    refine martingale_of_condExp_sub_eq_zero_nat hadapt hint (fun i => ?_)
    have hsub : f (i + 1) - f i = Z (i + 1) := by
      funext ω
      simp only [f, Pi.sub_apply, Finset.sum_range_succ _ (i + 1)]
      ring
    rw [hsub]
    refine (hindep.condExp_natural_ae_eq_of_lt hsm (Nat.lt_succ_self i)).trans ?_
    filter_upwards with ω
    simp [hmean]
  have hbdd : ∀ n, eLpNorm (f n) 1 μ
      ≤ ((Real.sqrt (∑' n, Var[Z n; μ])).toNNReal : ENNReal) := by
    intro n
    have hfun : f n = ∑ k ∈ Finset.range (n + 1), Z k := by
      funext ω; simp [f, Finset.sum_apply]
    have hL2f : MemLp (f n) 2 μ := by
      rw [hfun]; exact memLp_finsetSum' _ (fun k _ => hL2 k)
    have hmeanf : μ[f n] = 0 := by
      show ∫ ω, ∑ k ∈ Finset.range (n + 1), Z k ω ∂μ = 0
      rw [integral_finsetSum _ (fun k _ => (hL2 k).integrable one_le_two)]
      simp [hmean]
    have hvarf : Var[f n; μ] = ∑ k ∈ Finset.range (n + 1), Var[Z k; μ] := by
      rw [hfun]
      exact IndepFun.variance_sum (fun k _ => hL2 k) (fun i _ j _ hij => hindep.indepFun hij)
    have hle : Var[f n; μ] ≤ ∑' n, Var[Z n; μ] := by
      rw [hvarf]; exact hvar.sum_le_tsum _ (fun k _ => variance_nonneg _ _)
    have habs : (∫ ω, ‖f n ω‖ ∂μ) ^ 2 ≤ Var[f n; μ] := by
      have h1 := variance_nonneg (fun ω => ‖f n ω‖) μ
      rw [variance_eq_sub hL2f.norm] at h1
      rw [variance_eq_sub hL2f, hmeanf]
      have h3 : ∫ ω, ((fun ω => ‖f n ω‖) ^ 2) ω ∂μ = ∫ ω, (f n ^ 2) ω ∂μ := by
        congr 1; funext ω; simp [Real.norm_eq_abs, sq_abs]
      rw [h3] at h1
      linarith
    rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm (hint n)]
    show ENNReal.ofReal _ ≤ ENNReal.ofReal _
    refine ENNReal.ofReal_le_ofReal ?_
    refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
    exact habs.trans hle
  filter_upwards [hmart.submartingale.ae_tendsto_limitProcess hbdd] with ω hω
  refine ⟨ℱ.limitProcess f μ ω, ?_⟩
  rw [← Filter.tendsto_add_atTop_iff_nat 1]
  exact hω

open MeasureTheory ProbabilityTheory Filter DurrettProbability in
/-- Characteristic function of a finite sum of independent variables is the product. -/
lemma p2m40_charfun_sum {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → ℝ) (hY : ∀ n, Measurable (Y n)) (hind : iIndepFun Y μ) (t : ℝ) (N : ℕ) :
    ∫ ω, Complex.exp (t * (∑ n ∈ Finset.range N, Y n ω) * Complex.I) ∂μ
      = ∏ n ∈ Finset.range N, ∫ ω, Complex.exp (t * Y n ω * Complex.I) ∂μ := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.prod_range_succ, ← ih]
    have hI : IndepFun (∑ n ∈ Finset.range N, Y n) (Y N) μ :=
      hind.indepFun_finsetSum_of_notMem hY Finset.notMem_range_self
    have hg : Measurable (fun x : ℝ => Complex.exp (t * x * Complex.I)) := by fun_prop
    have := hI.integral_fun_comp_mul_comp (f := fun x : ℝ => Complex.exp (t * x * Complex.I))
      (g := fun x : ℝ => Complex.exp (t * x * Complex.I))
      (Finset.aemeasurable_sum _ (fun n _ => (hY n).aemeasurable)) (hY N).aemeasurable
      hg.aestronglyMeasurable hg.aestronglyMeasurable
    simp only [Finset.sum_apply] at this
    rw [← this]
    congr 1; funext ω
    rw [Finset.sum_range_succ, ← Complex.exp_add]; congr 1; push_cast; ring

open MeasureTheory ProbabilityTheory Filter DurrettProbability in
/-- `|φ_Y(t)|² ≤ 1 - (4/π²) t² Var Y` for `|Y| ≤ A`, `|t| A ≤ 1`. -/
lemma p2m40_charfun_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (Y : Ω → ℝ) (hY : Measurable Y) (A : ℝ) (hbd : ∀ ω, |Y ω| ≤ A) (t : ℝ) (ht : |t| * A ≤ 1) :
    ‖∫ ω, Complex.exp (t * Y ω * Complex.I) ∂μ‖ ^ 2
      ≤ 1 - 4 / Real.pi ^ 2 * t ^ 2 * Var[Y; μ] := by
  set a := ∫ ω, Real.cos (t * Y ω) ∂μ with ha
  set b := ∫ ω, Real.sin (t * Y ω) ∂μ with hb
  set m := ∫ ω, Y ω ∂μ with hm
  set s2 := ∫ ω, Y ω ^ 2 ∂μ with hs2
  have icos : Integrable (fun ω => Real.cos (t * Y ω)) μ :=
    p2m40_int_bdd _ (by fun_prop) 1 (fun ω => Real.abs_cos_le_one _)
  have isin : Integrable (fun ω => Real.sin (t * Y ω)) μ :=
    p2m40_int_bdd _ (by fun_prop) 1 (fun ω => Real.abs_sin_le_one _)
  have iY : Integrable Y μ := p2m40_int_bdd _ hY A hbd
  have iY2 : Integrable (fun ω => Y ω ^ 2) μ :=
    p2m40_int_bdd _ (by fun_prop) (A ^ 2) (fun ω => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hbd ω) 2)
  have hYL2 : MemLp Y 2 μ := MemLp.of_bound hY.aestronglyMeasurable A
    (ae_of_all _ (fun ω => by rw [Real.norm_eq_abs]; exact hbd ω))
  have hphi : ∫ ω, Complex.exp (t * Y ω * Complex.I) ∂μ = (a : ℂ) + (b : ℂ) * Complex.I := by
    have hpt : ∀ ω, Complex.exp (t * Y ω * Complex.I)
        = ((Real.cos (t * Y ω) : ℝ) : ℂ) + ((Real.sin (t * Y ω) : ℝ) : ℂ) * Complex.I := by
      intro ω
      rw [show (t : ℂ) * (Y ω : ℂ) = ((t * Y ω : ℝ) : ℂ) by push_cast; ring,
        Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
    simp_rw [hpt]
    rw [integral_add icos.ofReal (isin.ofReal.mul_const _), integral_mul_const,
      integral_complex_ofReal, integral_complex_ofReal]
  have hnorm : ‖(a : ℂ) + (b : ℂ) * Complex.I‖ ^ 2 = a ^ 2 + b ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_add_mul_I]
  have hdiff : ∀ ω ω', |t * Y ω - t * Y ω'| ≤ 2 := by
    intro ω ω'
    rw [← mul_sub, abs_mul]
    have h1 : |Y ω - Y ω'| ≤ A + A := (abs_sub _ _).trans (add_le_add (hbd ω) (hbd ω'))
    calc |t| * |Y ω - Y ω'| ≤ |t| * (A + A) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = 2 * (|t| * A) := by ring
      _ ≤ 2 := by linarith
  set c : ℝ := 2 / Real.pi ^ 2 with hc
  have hin1 : ∀ ω, ∫ ω', Real.cos (t * Y ω - t * Y ω') ∂μ
      = Real.cos (t * Y ω) * a + Real.sin (t * Y ω) * b := by
    intro ω
    simp_rw [Real.cos_sub]
    rw [integral_add (icos.const_mul _) (isin.const_mul _), integral_const_mul, integral_const_mul]
  have hin2 : ∀ ω, ∫ ω', ((1 - c * t ^ 2 * Y ω ^ 2) + (2 * c * t ^ 2 * Y ω) * Y ω'
        - (c * t ^ 2) * Y ω' ^ 2) ∂μ
      = 1 - c * t ^ 2 * (Y ω ^ 2 - 2 * Y ω * m + s2) := by
    intro ω
    have i0 : Integrable (fun _ : Ω => (1 - c * t ^ 2 * Y ω ^ 2)) μ := integrable_const _
    have i1 : Integrable (fun ω' => (2 * c * t ^ 2 * Y ω) * Y ω') μ := iY.const_mul _
    have i2 : Integrable (fun ω' => (c * t ^ 2) * Y ω' ^ 2) μ := iY2.const_mul _
    have i01 : Integrable (fun ω' => (1 - c * t ^ 2 * Y ω ^ 2) + (2 * c * t ^ 2 * Y ω) * Y ω') μ :=
      i0.add i1
    rw [integral_sub i01 i2, integral_add i0 i1, integral_const, integral_const_mul,
      integral_const_mul]
    simp only [probReal_univ, one_smul]
    ring
  have hpt : ∀ ω, Real.cos (t * Y ω) * a + Real.sin (t * Y ω) * b
      ≤ 1 - c * t ^ 2 * (Y ω ^ 2 - 2 * Y ω * m + s2) := by
    intro ω
    rw [← hin1, ← hin2]
    refine integral_mono (p2m40_int_bdd _ (by fun_prop) 1 (fun _ => Real.abs_cos_le_one _))
      (((integrable_const _).add (iY.const_mul _)).sub (iY2.const_mul _)) (fun ω' => ?_)
    have h1 := Real.cos_le_one_sub_mul_cos_sq
      (le_trans (hdiff ω ω') (by linarith [Real.pi_gt_three]) : |t * Y ω - t * Y ω'| ≤ Real.pi)
    have h2 : 1 - 2 / Real.pi ^ 2 * (t * Y ω - t * Y ω') ^ 2
        = (1 - c * t ^ 2 * Y ω ^ 2) + (2 * c * t ^ 2 * Y ω) * Y ω' - (c * t ^ 2) * Y ω' ^ 2 := by
      rw [hc]; ring
    rw [h2] at h1
    exact h1
  have hfinal : a ^ 2 + b ^ 2 ≤ 1 - 2 * c * t ^ 2 * (s2 - m ^ 2) := by
    have h1 : ∫ ω, (Real.cos (t * Y ω) * a + Real.sin (t * Y ω) * b) ∂μ = a ^ 2 + b ^ 2 := by
      rw [integral_add (icos.mul_const _) (isin.mul_const _), integral_mul_const,
        integral_mul_const]
      ring
    have h2 : ∫ ω, (1 - c * t ^ 2 * (Y ω ^ 2 - 2 * Y ω * m + s2)) ∂μ
        = 1 - 2 * c * t ^ 2 * (s2 - m ^ 2) := by
      have e : ∀ ω, (1 - c * t ^ 2 * (Y ω ^ 2 - 2 * Y ω * m + s2))
          = (1 - c * t ^ 2 * s2) + (2 * c * t ^ 2 * m) * Y ω - (c * t ^ 2) * Y ω ^ 2 := by
        intro ω; ring
      simp_rw [e]
      have i0 : Integrable (fun _ : Ω => (1 - c * t ^ 2 * s2)) μ := integrable_const _
      have i1 : Integrable (fun ω => (2 * c * t ^ 2 * m) * Y ω) μ := iY.const_mul _
      have i2 : Integrable (fun ω => (c * t ^ 2) * Y ω ^ 2) μ := iY2.const_mul _
      have i01 : Integrable (fun ω => (1 - c * t ^ 2 * s2) + (2 * c * t ^ 2 * m) * Y ω) μ :=
        i0.add i1
      rw [integral_sub i01 i2, integral_add i0 i1, integral_const, integral_const_mul,
        integral_const_mul]
      simp only [probReal_univ, one_smul]
      ring
    rw [← h1, ← h2]
    refine integral_mono ((icos.mul_const _).add (isin.mul_const _)) ?_ hpt
    have iP := ((integrable_const (1 - c * t ^ 2 * s2)).add (iY.const_mul (2 * c * t ^ 2 * m))).sub
      (iY2.const_mul (c * t ^ 2))
    refine iP.congr (ae_of_all _ (fun ω => ?_))
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hv : Var[Y; μ] = s2 - m ^ 2 := by
    rw [variance_eq_sub hYL2]; rfl
  rw [hphi, hnorm, hv]
  have : 4 / Real.pi ^ 2 = 2 * c := by rw [hc]; ring
  rw [this]
  exact hfinal

open MeasureTheory ProbabilityTheory Filter DurrettProbability in
/-- Necessity of the variance condition for bounded independent summands (via characteristic
functions). -/
lemma p2m40_var_summable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → ℝ) (hY : ∀ n, Measurable (Y n)) (hind : iIndepFun Y μ) (A : ℝ) (hA : 0 < A)
    (hbd : ∀ n ω, |Y n ω| ≤ A)
    (hconv : ∀ᵐ ω ∂μ, ∃ L : ℝ, Tendsto (fun N => ∑ n ∈ Finset.range N, Y n ω) atTop (nhds L)) :
    Summable (fun n => Var[Y n; μ]) := by
  by_contra hns
  have hV : Tendsto (fun N => ∑ n ∈ Finset.range N, Var[Y n; μ]) atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg (fun n => variance_nonneg _ _)).1 hns
  let S : Ω → ℝ := fun ω => limUnder atTop (fun N => ∑ n ∈ Finset.range N, Y n ω)
  have hS : ∀ᵐ ω ∂μ, Tendsto (fun N => ∑ n ∈ Finset.range N, Y n ω) atTop (nhds (S ω)) := by
    filter_upwards [hconv] with ω hω
    exact tendsto_nhds_limUnder hω
  have hsumm : ∀ N, Measurable (fun ω => ∑ n ∈ Finset.range N, Y n ω) := fun N =>
    Finset.measurable_fun_sum _ (fun n _ => hY n)
  have hSm : AEStronglyMeasurable S μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun N => (hsumm N).aestronglyMeasurable) hS
  have hn : ∀ (t x : ℝ), ‖Complex.exp (t * x * Complex.I)‖ = 1 := by
    intro t x; rw [← Complex.ofReal_mul]; exact Complex.norm_exp_ofReal_mul_I _
  have hexp_meas : ∀ (t : ℝ) (F : Ω → ℝ), AEStronglyMeasurable F μ →
      AEStronglyMeasurable (fun ω => Complex.exp (t * F ω * Complex.I)) μ := by
    intro t F hF
    exact (by fun_prop : Continuous fun x : ℝ => Complex.exp (t * x * Complex.I)).comp_aestronglyMeasurable hF
  have hzero : ∀ t : ℝ, 0 < t → t * A ≤ 1 →
      ∫ ω, Complex.exp (t * S ω * Complex.I) ∂μ = 0 := by
    intro t ht0 htA
    have h1 : Tendsto (fun N => ∫ ω, Complex.exp (t * (∑ n ∈ Finset.range N, Y n ω) * Complex.I) ∂μ)
        atTop (nhds (∫ ω, Complex.exp (t * S ω * Complex.I) ∂μ)) := by
      refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
        (fun N => hexp_meas t _ (hsumm N).aestronglyMeasurable) (integrable_const 1)
        (fun N => ae_of_all _ (fun ω => le_of_eq (hn _ _))) ?_
      filter_upwards [hS] with ω hω
      exact ((by fun_prop : Continuous fun x : ℝ => Complex.exp (t * x * Complex.I)).tendsto _).comp hω
    have h2 : Tendsto (fun N => ‖∫ ω, Complex.exp (t * (∑ n ∈ Finset.range N, Y n ω) * Complex.I) ∂μ‖ ^ 2)
        atTop (nhds 0) := by
      have hup : ∀ N, ‖∫ ω, Complex.exp (t * (∑ n ∈ Finset.range N, Y n ω) * Complex.I) ∂μ‖ ^ 2
          ≤ Real.exp (-(4 / Real.pi ^ 2 * t ^ 2) * ∑ n ∈ Finset.range N, Var[Y n; μ]) := by
        intro N
        rw [p2m40_charfun_sum Y hY hind t N, norm_prod, ← Finset.prod_pow, Finset.mul_sum,
          Real.exp_sum]
        refine Finset.prod_le_prod (fun n _ => by positivity) (fun n _ => ?_)
        refine (p2m40_charfun_bound (Y n) (hY n) A (hbd n) t
          (by rw [abs_of_pos ht0]; exact htA)).trans ?_
        have := Real.add_one_le_exp (-(4 / Real.pi ^ 2 * t ^ 2) * Var[Y n; μ])
        linarith
      have hneg : -(4 / Real.pi ^ 2 * t ^ 2) < 0 := by
        have : 0 < 4 / Real.pi ^ 2 * t ^ 2 := by positivity
        linarith
      have hlim : Tendsto (fun N => Real.exp (-(4 / Real.pi ^ 2 * t ^ 2)
          * ∑ n ∈ Finset.range N, Var[Y n; μ])) atTop (nhds 0) :=
        Real.tendsto_exp_atBot.comp (hV.const_mul_atTop_of_neg hneg)
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
        (fun N => by positivity) hup
    have h3 := (h1.norm.pow 2)
    have h4 := tendsto_nhds_unique h3 h2
    exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h4)
  let tm : ℕ → ℝ := fun m => 1 / A * (1 / ((m : ℝ) + 1))
  have htm : Tendsto tm atTop (nhds 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (1 / A)
    simpa [tm] using this
  have h5 : Tendsto (fun m : ℕ => ∫ ω, Complex.exp ((tm m : ℝ) * S ω * Complex.I) ∂μ) atTop
      (nhds (∫ ω, Complex.exp (((0 : ℝ) : ℂ) * S ω * Complex.I) ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
      (fun m => hexp_meas _ _ hSm) (integrable_const 1)
      (fun m => ae_of_all _ (fun ω => le_of_eq (hn _ _))) (ae_of_all _ (fun ω => ?_))
    exact ((by fun_prop : Continuous fun s : ℝ => Complex.exp (s * S ω * Complex.I)).tendsto 0).comp htm
  have h6 : (fun m : ℕ => ∫ ω, Complex.exp ((tm m : ℝ) * S ω * Complex.I) ∂μ) = fun _ => 0 := by
    funext m
    apply hzero
    · positivity
    · have : tm m * A = 1 / ((m : ℝ) + 1) := by
        simp only [tm]; field_simp
      rw [this]
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
  rw [h6] at h5
  have h7 : ∫ ω, Complex.exp (((0 : ℝ) : ℂ) * S ω * Complex.I) ∂μ = 1 := by simp
  rw [h7] at h5
  exact one_ne_zero (tendsto_nhds_unique h5 tendsto_const_nhds)

open MeasureTheory ProbabilityTheory Filter DurrettProbability in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hmeas : ∀ i, Measurable (X i))
    (hindep : iIndepFun X μ) (A : ℝ) (hA : 0 < A) :
    SeriesConvergesAE X μ ↔
      (Summable (fun n => (μ {ω | A < |X n ω|}).toReal)
        ∧ (∃ L : ℝ, Tendsto (fun N => ∑ n ∈ Finset.range N, μ[truncate A (X n)]) atTop (nhds L))
        ∧ Summable (fun n => Var[truncate A (X n); μ])) := by
  set Y : ℕ → Ω → ℝ := fun n => truncate A (X n) with hYdef
  have htr : Measurable (fun x : ℝ => if |x| ≤ A then x else 0) := by
    refine Measurable.ite ?_ measurable_id measurable_const
    exact measurableSet_le measurable_abs measurable_const
  have hYm : ∀ n, Measurable (Y n) := fun n => htr.comp (hmeas n)
  have hYind : iIndepFun Y μ := hindep.comp (fun _ x => if |x| ≤ A then x else 0) (fun _ => htr)
  have hYbd : ∀ n ω, |Y n ω| ≤ A := by
    intro n ω
    simp only [Y, truncate]
    split_ifs with h
    · exact h
    · simp [hA.le]
  have hYL2 : ∀ n, MemLp (Y n) 2 μ := fun n => MemLp.of_bound (hYm n).aestronglyMeasurable A
    (ae_of_all _ (fun ω => by rw [Real.norm_eq_abs]; exact hYbd n ω))
  set Z : ℕ → Ω → ℝ := fun n ω => Y n ω - μ[Y n] with hZdef
  have hZm : ∀ n, Measurable (Z n) := fun n => (hYm n).sub_const _
  have hZind : iIndepFun Z μ := by
    have h := hindep.comp (fun n (x : ℝ) => (if |x| ≤ A then x else 0) - ∫ ω, Y n ω ∂μ)
      (fun n => htr.sub_const _)
    have hZeq : Z = fun n => (fun (x : ℝ) => (if |x| ≤ A then x else 0) - ∫ ω, Y n ω ∂μ) ∘ X n := by
      funext n ω; rfl
    rw [hZeq]; exact h
  have hZL2 : ∀ n, MemLp (Z n) 2 μ := fun n => (hYL2 n).sub (memLp_const _)
  have hZmean : ∀ n, μ[Z n] = 0 := by
    intro n
    show ∫ ω, (Y n ω - μ[Y n]) ∂μ = 0
    rw [integral_sub ((hYL2 n).integrable one_le_two) (integrable_const _)]
    simp
  have hZvar : ∀ n, Var[Z n; μ] = Var[Y n; μ] := fun n =>
    variance_sub_const (hYm n).aestronglyMeasurable _
  set s : ℕ → Set Ω := fun n => {ω | A < |X n ω|} with hsdef
  have hsm : ∀ n, MeasurableSet (s n) := fun n =>
    measurableSet_lt measurable_const ((hmeas n).abs)
  constructor
  · intro hconv
    have hX0 : ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, ω ∉ s n := by
      filter_upwards [hconv] with ω hω
      obtain ⟨L, hL⟩ := hω
      have h1 : Tendsto (fun n => partialSum X (n + 1) ω - partialSum X n ω) atTop
          (nhds (L - L)) := ((tendsto_add_atTop_iff_nat 1).2 hL).sub hL
      have h2 : (fun n => partialSum X (n + 1) ω - partialSum X n ω) = fun n => X n ω := by
        funext n; simp [partialSum, Finset.sum_range_succ]
      rw [h2, sub_self] at h1
      filter_upwards [h1.eventually (Metric.ball_mem_nhds 0 hA)] with n hn
      simp only [Real.dist_eq, sub_zero] at hn
      simp only [s, Set.mem_ofPred_eq, not_lt]
      exact hn.le
    have hs1 : Summable (fun n => (μ (s n)).toReal) := by
      by_contra hns
      have htop : ∑' n, μ (s n) = ⊤ := by
        by_contra hne; exact hns (ENNReal.summable_toReal hne)
      have hind_s : iIndepSet s μ := by
        rw [iIndepSet_iff_iIndep]
        rw [iIndepFun_iff_iIndep] at hindep
        refine iIndep_of_iIndep_of_le hindep (fun n => ?_)
        refine MeasurableSpace.generateFrom_le (fun t ht => ?_)
        rw [Set.mem_singleton_iff.1 ht]
        exact ⟨{x | A < |x|}, measurableSet_lt measurable_const measurable_abs, rfl⟩
      have h1 := measure_limsup_eq_one hsm hind_s htop
      have h0 : μ (limsup s atTop) = 0 := by
        rw [measure_eq_zero_iff_ae_notMem]
        filter_upwards [hX0] with ω hω
        rw [mem_limsup_iff_frequently_mem]
        exact not_frequently.2 hω
      rw [h0] at h1
      exact zero_ne_one h1
    have hYconv : ∀ᵐ ω ∂μ, ∃ L : ℝ,
        Tendsto (fun N => ∑ n ∈ Finset.range N, Y n ω) atTop (nhds L) := by
      filter_upwards [hconv, hX0] with ω hω hω0
      obtain ⟨L, hL⟩ := hω
      obtain ⟨n0, hn0⟩ := eventually_atTop.1 hω0
      exact p2m40_sum_congr_tail (fun n => Y n ω) (fun n => X n ω) n0 (fun n hn => by
        have := hn0 n hn
        simp only [s, Set.mem_ofPred_eq, not_lt] at this
        simp [Y, truncate, this]) L hL
    have hvarY : Summable (fun n => Var[Y n; μ]) :=
      p2m40_var_summable Y hYm hYind A hA hYbd hYconv
    have hZconv := p2m40_centered Z hZm hZind hZL2 hZmean
      (hvarY.congr (fun n => (hZvar n).symm))
    obtain ⟨ω, ⟨L1, h1⟩, ⟨L2, h2⟩⟩ := (hYconv.and hZconv).exists
    refine ⟨hs1, ⟨L1 - L2, ?_⟩, hvarY⟩
    refine (h1.sub h2).congr (fun N => ?_)
    simp only [Z, Finset.sum_sub_distrib]
    ring
  · rintro ⟨hs1, ⟨Lm, hLm⟩, hvarY⟩
    have hZconv := p2m40_centered Z hZm hZind hZL2 hZmean
      (hvarY.congr (fun n => (hZvar n).symm))
    have hne : ∑' n, μ (s n) ≠ ⊤ := by
      have : ∀ n, μ (s n) = ENNReal.ofReal ((μ (s n)).toReal) := fun n =>
        (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
      rw [tsum_congr this, ← ENNReal.ofReal_tsum_of_nonneg (fun n => ENNReal.toReal_nonneg) hs1]
      exact ENNReal.ofReal_ne_top
    have hev := ae_eventually_notMem hne
    show ∀ᵐ ω ∂μ, ∃ L : ℝ, Tendsto (fun N => partialSum X N ω) atTop (nhds L)
    filter_upwards [hZconv, hev] with ω hω hω0
    obtain ⟨L2, h2⟩ := hω
    obtain ⟨n0, hn0⟩ := eventually_atTop.1 hω0
    have hYω : Tendsto (fun N => ∑ n ∈ Finset.range N, Y n ω) atTop (nhds (L2 + Lm)) := by
      refine (h2.add hLm).congr (fun N => ?_)
      simp only [Z, Finset.sum_sub_distrib]
      ring
    exact p2m40_sum_congr_tail (fun n => X n ω) (fun n => Y n ω) n0 (fun n hn => by
      have := hn0 n hn
      simp only [s, Set.mem_ofPred_eq, not_lt] at this
      simp [Y, truncate, this]) _ hYω
