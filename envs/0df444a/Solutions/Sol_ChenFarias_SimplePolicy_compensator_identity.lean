-- Prove2me | solution 1 for ChenFarias.SimplePolicy.compensator_identity
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T19:06:18.007125+00:00
-- url     : https://prove2.me/submissions/1423efc0-4c34-49da-b61f-22e825288b55

import Mathlib
import Definitions.Def_ChenFarias_SimplePolicy_Model
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
open ChenFarias.SimplePolicy

lemma cf_lintegral_expMeasure (β : ℝ) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ s, g s ∂expMeasure β =
      ∫⁻ s in Ici 0, ENNReal.ofReal (β * Real.exp (-(β * s))) * g s := by
  have hpdf : Measurable (exponentialPDF β) :=
    (measurable_exponentialPDFReal β).ennreal_ofReal
  have : expMeasure β = volume.withDensity (exponentialPDF β) := rfl
  rw [this, lintegral_withDensity_eq_lintegral_mul _ hpdf hg]
  have hind : (exponentialPDF β * g) =
      (Ici (0:ℝ)).indicator (fun s => ENNReal.ofReal (β * Real.exp (-(β * s))) * g s) := by
    funext s
    by_cases hs : 0 ≤ s
    · simp [Set.indicator_of_mem (show s ∈ Ici (0:ℝ) from hs), exponentialPDF_of_nonneg hs]
    · push Not at hs
      simp [Set.indicator_of_notMem (show s ∉ Ici (0:ℝ) from not_le.2 hs),
        exponentialPDF_of_neg hs]
  rw [hind, lintegral_indicator measurableSet_Ici]

lemma cf_lintegral_Ioi_FTC {g g' : ℝ → ℝ} {a l : ℝ}
    (hderiv : ∀ x ∈ Ici a, HasDerivAt g (g' x) x) (hpos : ∀ x ∈ Ioi a, 0 ≤ g' x)
    (hg : Tendsto g atTop (𝓝 l)) :
    ∫⁻ x in Ioi a, ENNReal.ofReal (g' x) = ENNReal.ofReal (l - g a) := by
  have hint := integrableOn_Ioi_deriv_of_nonneg' hderiv hpos hg
  rw [← integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos hg,
    ofReal_integral_eq_lintegral_ofReal hint]
  exact (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hpos)

lemma cf_expMeasure_Iio (r : ℝ) : expMeasure r (Iio 0) = 0 := by
  have : expMeasure r = volume.withDensity (exponentialPDF r) := rfl
  rw [this, withDensity_apply _ measurableSet_Iio]
  rw [setLIntegral_congr_fun measurableSet_Iio (g := fun _ => 0)
    (fun x hx => exponentialPDF_of_neg hx)]
  simp

/-- Tail of the exponential law. -/
lemma cf_expMeasure_Ici (β a : ℝ) (hβ : 0 < β) (ha : 0 ≤ a) :
    expMeasure β (Ici a) = ENNReal.ofReal (Real.exp (-(β * a))) := by
  rw [← lintegral_indicator_one measurableSet_Ici,
    cf_lintegral_expMeasure β (g := (Ici a).indicator 1)
      ((measurable_const).indicator measurableSet_Ici)]
  have h1 : (fun s => ENNReal.ofReal (β * Real.exp (-(β * s))) * (Ici a).indicator 1 s) =
      (Ici a).indicator (fun s => ENNReal.ofReal (β * Real.exp (-(β * s)))) := by
    funext s
    by_cases hs : s ∈ Ici a
    · simp [Set.indicator_of_mem hs]
    · simp [Set.indicator_of_notMem hs]
  rw [h1, lintegral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
    show Ici a ∩ Ici (0:ℝ) = Ici a from inter_eq_left.2 (Ici_subset_Ici.2 ha),
    ← setLIntegral_congr Ioi_ae_eq_Ici]
  have hderiv : ∀ x ∈ Ici a, HasDerivAt (fun s => -Real.exp (-(β * s)))
      (β * Real.exp (-(β * x))) x := by
    intro x _
    have := (((hasDerivAt_id x).const_mul β).neg.exp).neg
    refine this.congr_deriv ?_
    simp only [Pi.neg_apply, id, mul_one]; ring
  have hpos : ∀ x ∈ Ioi a, 0 ≤ β * Real.exp (-(β * x)) := fun x _ => by positivity
  have htend : Tendsto (fun s => -Real.exp (-(β * s))) atTop (𝓝 0) := by
    have := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hβ)
    simpa [Function.comp_def] using this.neg
  rw [cf_lintegral_Ioi_FTC hderiv hpos htend]
  congr 1; ring

lemma cf_clock_ae_nonneg (x0 : ℕ) : ∀ᵐ e ∂clockLaw x0, ∀ i, 0 ≤ e i := by
  rw [ae_all_iff]
  intro i
  have h : ∀ᵐ y ∂expMeasure 1, 0 ≤ y := by
    rw [ae_iff]
    have := cf_expMeasure_Iio 1
    simpa [not_le, Iio] using this
  have : IsProbabilityMeasure (expMeasure (1:ℝ)) := isProbabilityMeasure_expMeasure one_pos
  exact Measure.tendsto_eval_ae_ae.eventually h

lemma cf_saleTime_measurable (lam : ℝ) (f : ℝ → ℝ) (π : ℕ → ℝ) (x0 k : ℕ) :
    Measurable (saleTime lam f π x0 k) := by
  unfold saleTime
  exact Finset.measurable_sum _ (fun i _ => (measurable_pi_apply i).div_const _)

lemma cf_saleTime_nonneg (lam : ℝ) (f : ℝ → ℝ) (π : ℕ → ℝ) (x0 k : ℕ)
    (hlam : 0 < lam) (hf : Assumption1 f) (e : Fin x0 → ℝ) (he : ∀ i, 0 ≤ e i) :
    0 ≤ saleTime lam f π x0 k e := by
  unfold saleTime
  refine Finset.sum_nonneg (fun i _ => div_nonneg (he i) (mul_nonneg hlam.le ?_))
  exact setIntegral_nonneg measurableSet_Ioi (fun v _ => hf.nonnegative v)

lemma cf_clockLaw_prob (x0 : ℕ) : IsProbabilityMeasure (clockLaw x0) := by
  have : IsProbabilityMeasure (expMeasure (1:ℝ)) := isProbabilityMeasure_expMeasure one_pos
  unfold clockLaw
  infer_instance

lemma cf_expMeasure_Ioi (β a : ℝ) (hβ : 0 < β) (ha : 0 ≤ a) :
    expMeasure β (Ioi a) = ENNReal.ofReal (Real.exp (-(β * a))) := by
  rw [← lintegral_indicator_one measurableSet_Ioi,
    cf_lintegral_expMeasure β (g := (Ioi a).indicator 1)
      ((measurable_const).indicator measurableSet_Ioi)]
  have h1 : (fun s => ENNReal.ofReal (β * Real.exp (-(β * s))) * (Ioi a).indicator 1 s) =
      (Ioi a).indicator (fun s => ENNReal.ofReal (β * Real.exp (-(β * s)))) := by
    funext s
    by_cases hs : s ∈ Ioi a
    · simp [Set.indicator_of_mem hs]
    · simp [Set.indicator_of_notMem hs]
  rw [h1, lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    show Ioi a ∩ Ici (0:ℝ) = Ioi a from inter_eq_left.2 (fun x hx => le_of_lt (lt_of_le_of_lt ha hx))]
  have hderiv : ∀ x ∈ Ici a, HasDerivAt (fun s => -Real.exp (-(β * s)))
      (β * Real.exp (-(β * x))) x := by
    intro x _
    have := (((hasDerivAt_id x).const_mul β).neg.exp).neg
    refine this.congr_deriv ?_
    simp only [Pi.neg_apply, id, mul_one]; ring
  have hpos : ∀ x ∈ Ioi a, 0 ≤ β * Real.exp (-(β * x)) := fun x _ => by positivity
  have htend : Tendsto (fun s => -Real.exp (-(β * s))) atTop (𝓝 0) := by
    have := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hβ)
    simpa [Function.comp_def] using this.neg
  rw [cf_lintegral_Ioi_FTC hderiv hpos htend]
  congr 1; ring

lemma cf_expMeasure_Iic_zero : expMeasure 1 (Iic (0:ℝ)) = 0 := by
  have h : Iic (0:ℝ) = Iio 0 ∪ {0} := by
    ext x; simp [le_iff_lt_or_eq]
  have hs : expMeasure 1 ({0} : Set ℝ) = 0 := by
    have : expMeasure (1:ℝ) = volume.withDensity (exponentialPDF 1) := rfl
    rw [this, withDensity_apply _ (measurableSet_singleton 0),
      Measure.restrict_eq_zero.2 Real.volume_singleton, lintegral_zero_measure]
  apply le_antisymm _ bot_le
  calc expMeasure 1 (Iic (0:ℝ)) ≤ expMeasure 1 (Iio 0) + expMeasure 1 {0} := by
        rw [h]; exact measure_union_le _ _
    _ = 0 := by rw [cf_expMeasure_Iio, hs, add_zero]

/-- `E[(Y - L)^+] = e^{-L}` for `Y ~ Exp(1)` and `L ≥ 0`. -/
lemma cf_exp_excess (L : ℝ) (hL : 0 ≤ L) :
    ∫⁻ y, ENNReal.ofReal (max (y - L) 0) ∂expMeasure 1 = ENNReal.ofReal (Real.exp (-L)) := by
  have hmeas : Measurable (fun y : ℝ => ENNReal.ofReal (max (y - L) 0)) := by fun_prop
  rw [cf_lintegral_expMeasure 1 hmeas]
  have hrestr : ∫⁻ s in Ici 0, ENNReal.ofReal (1 * Real.exp (-(1 * s))) *
        ENNReal.ofReal (max (s - L) 0) =
      ∫⁻ s in Ioi L, ENNReal.ofReal ((s - L) * Real.exp (-s)) := by
    rw [← lintegral_indicator measurableSet_Ici, ← lintegral_indicator measurableSet_Ioi]
    congr 1
    funext s
    by_cases h1 : s ∈ Ioi L
    · have hs0 : s ∈ Ici (0:ℝ) := le_of_lt (lt_of_le_of_lt hL h1)
      rw [Set.indicator_of_mem h1, Set.indicator_of_mem hs0]
      have : 0 ≤ s - L := by simp at h1; linarith
      rw [max_eq_left this, ← ENNReal.ofReal_mul (by positivity)]
      congr 1; ring
    · rw [Set.indicator_of_notMem h1]
      by_cases h2 : s ∈ Ici (0:ℝ)
      · rw [Set.indicator_of_mem h2]
        have : s - L ≤ 0 := by simp at h1; linarith
        simp [max_eq_right this]
      · rw [Set.indicator_of_notMem h2]
  rw [hrestr]
  set g : ℝ → ℝ := fun s => -((s - L + 1) * Real.exp (-s)) with hgdef
  have hderiv : ∀ x ∈ Ici L, HasDerivAt g ((x - L) * Real.exp (-x)) x := by
    intro x _
    have h1 : HasDerivAt (fun s : ℝ => s - L + 1) 1 x :=
      ((hasDerivAt_id x).sub_const L).add_const 1
    have h2 : HasDerivAt (fun s : ℝ => Real.exp (-s)) (Real.exp (-x) * (-1)) x := by
      have := (hasDerivAt_id x).neg.exp
      simpa using this
    have h3 : HasDerivAt (fun s => -((s - L + 1) * Real.exp (-s)))
        (-(1 * Real.exp (-x) + (x - L + 1) * (Real.exp (-x) * (-1)))) x := (h1.mul h2).neg
    refine h3.congr_deriv ?_
    ring
  have hpos : ∀ x ∈ Ioi L, 0 ≤ (x - L) * Real.exp (-x) := by
    intro x hx
    have : 0 ≤ x - L := by simp at hx; linarith
    positivity
  have htend : Tendsto g atTop (𝓝 0) := by
    have hA : Tendsto (fun s : ℝ => s * Real.exp (-1 * s)) atTop (𝓝 0) := by
      simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 1 one_pos
    have hB : Tendsto (fun s : ℝ => Real.exp (-s)) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero
    have := (hA.add (hB.const_mul (-L + 1))).neg
    simp only [mul_zero, add_zero, neg_zero] at this
    refine this.congr (fun s => ?_)
    simp only [hgdef, neg_mul, one_mul]
    ring
  rw [cf_lintegral_Ioi_FTC hderiv hpos htend]
  congr 1
  simp only [hgdef, sub_self, zero_add, one_mul, zero_sub, neg_neg]

/-- Single-clock form of the compensator identity. -/
lemma cf_single_clock (a μ T : ℝ) (hμ : 0 < μ) :
    ∫⁻ y, ENNReal.ofReal (μ * (min (a + y / μ) T - a)) ∂expMeasure 1 =
      expMeasure 1 {y | a + y / μ ≤ T} := by
  have hexp1 : IsProbabilityMeasure (expMeasure (1:ℝ)) := isProbabilityMeasure_expMeasure one_pos
  rcases le_or_gt T a with haT | haT
  · have h0 : ∀ y, ENNReal.ofReal (μ * (min (a + y / μ) T - a)) = 0 := by
      intro y
      apply ENNReal.ofReal_of_nonpos
      have : min (a + y / μ) T - a ≤ 0 := by
        have := min_le_right (a + y / μ) T; linarith
      exact mul_nonpos_of_nonneg_of_nonpos hμ.le this
    simp_rw [h0, lintegral_zero]
    symm
    apply measure_mono_null _ cf_expMeasure_Iic_zero
    intro y hy
    simp only [mem_ofPred_eq] at hy
    simp only [mem_Iic]
    by_contra hy0
    push Not at hy0
    have := div_pos hy0 hμ
    linarith
  · set L := μ * (T - a) with hLdef
    have hL : 0 < L := mul_pos hμ (by linarith)
    have hint : ∀ y, μ * (min (a + y / μ) T - a) = min y L := by
      intro y
      rcases le_total (a + y / μ) T with h | h
      · rw [min_eq_left h]
        have h' : y / μ ≤ T - a := by linarith
        have : y ≤ L := by rw [hLdef]; have := (div_le_iff₀ hμ).1 h'; linarith
        rw [min_eq_left this]
        field_simp
        ring
      · rw [min_eq_right h]
        have h' : T - a ≤ y / μ := by linarith
        have : L ≤ y := by rw [hLdef]; have := (le_div_iff₀ hμ).1 h'; linarith
        rw [min_eq_right this]
    have hset : {y : ℝ | a + y / μ ≤ T} = Iic L := by
      ext y
      simp only [mem_setOf_eq, mem_Iic, hLdef]
      constructor
      · intro h
        have h' : y / μ ≤ T - a := by linarith
        have := (div_le_iff₀ hμ).1 h'; linarith
      · intro h
        have : y / μ ≤ T - a := (div_le_iff₀ hμ).2 (by linarith)
        linarith
    simp_rw [hint]
    rw [hset]
    have hsum1 : (∫⁻ y, ENNReal.ofReal (min y L) ∂expMeasure 1) +
        ENNReal.ofReal (Real.exp (-L)) = 1 := by
      rw [← cf_exp_excess L hL.le, ← lintegral_add_left (by fun_prop)]
      have hpt : ∀ y : ℝ, ENNReal.ofReal (min y L) + ENNReal.ofReal (max (y - L) 0) =
          ENNReal.ofReal (max (y - 0) 0) := by
        intro y
        rcases le_total y 0 with hy | hy
        · rw [ENNReal.ofReal_of_nonpos (le_trans (min_le_left _ _) hy),
            max_eq_right (by linarith), max_eq_right (by linarith)]
          simp
        · rcases le_total y L with hyL | hyL
          · rw [min_eq_left hyL, max_eq_right (by linarith), sub_zero, max_eq_left hy]
            simp
          · rw [min_eq_right hyL, max_eq_left (by linarith), sub_zero, max_eq_left hy,
              ← ENNReal.ofReal_add hL.le (by linarith)]
            congr 1; ring
      simp_rw [hpt]
      rw [cf_exp_excess 0 le_rfl]
      simp
    have hsum2 : expMeasure 1 (Iic L) + ENNReal.ofReal (Real.exp (-L)) = 1 := by
      have := cf_expMeasure_Ioi 1 L one_pos hL.le
      rw [one_mul] at this
      rw [← this, ← compl_Iic, measure_add_measure_compl measurableSet_Iic, measure_univ]
    exact (ENNReal.add_left_inj ENNReal.ofReal_ne_top).1 (hsum1.trans hsum2.symm)

lemma cf_filter_Icc (P : ℕ → Prop) [DecidablePred P] (hP : ∀ j j', j ≤ j' → P j' → P j)
    (n : ℕ) : ∃ m ≤ n, (Finset.Icc 1 n).filter P = Finset.Icc 1 m := by
  induction n with
  | zero => exact ⟨0, le_rfl, by simp⟩
  | succ n ih =>
    obtain ⟨m, hm, h⟩ := ih
    by_cases hn : P (n + 1)
    · refine ⟨n + 1, le_rfl, ?_⟩
      ext j
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · exact fun h => h.1
      · intro hj; exact ⟨hj, hP j (n + 1) hj.2 hn⟩
    · refine ⟨m, by omega, ?_⟩
      rw [← h]
      ext j
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨⟨h1, ?_⟩, h3⟩
        by_contra hc
        have : j = n + 1 := by omega
        exact hn (this ▸ h3)
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨⟨h1, by omega⟩, h3⟩

lemma cf_saleTime_zero (lam : ℝ) (f : ℝ → ℝ) (π : ℕ → ℝ) (x0 : ℕ) (e : Fin x0 → ℝ) :
    saleTime lam f π x0 0 e = 0 := by
  unfold saleTime
  simp

lemma cf_saleTime_mono (lam : ℝ) (f : ℝ → ℝ) (π : ℕ → ℝ) (x0 : ℕ)
    (hlam : 0 < lam) (hf : Assumption1 f) (e : Fin x0 → ℝ) (he : ∀ i, 0 ≤ e i)
    {j j' : ℕ} (hjj : j ≤ j') :
    saleTime lam f π x0 j e ≤ saleTime lam f π x0 j' e := by
  unfold saleTime
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    simp only [Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, by omega⟩
  · intro i _ _
    exact div_nonneg (he i) (mul_nonneg hlam.le
      (setIntegral_nonneg measurableSet_Ioi (fun v _ => hf.nonnegative v)))

lemma cf_saleTime_succ (lam : ℝ) (f : ℝ → ℝ) (π : ℕ → ℝ) (x0 k : ℕ) (hk : k < x0)
    (e : Fin x0 → ℝ) :
    saleTime lam f π x0 (k + 1) e =
      saleTime lam f π x0 k e + e ⟨k, hk⟩ / (lam * Fbar f (π (x0 - k))) := by
  unfold saleTime
  have hset : Finset.univ.filter (fun i : Fin x0 => i.val < k + 1) =
      insert ⟨k, hk⟩ (Finset.univ.filter (fun i : Fin x0 => i.val < k)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro h
      rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
      · exact Or.inr h
      · exact Or.inl (Fin.ext h)
    · rintro (h | h)
      · rw [h]; simp
      · omega
  rw [hset, Finset.sum_insert (by simp), add_comm]

lemma cf_saleTime_update (lam : ℝ) (f : ℝ → ℝ) (π : ℕ → ℝ) (x0 k : ℕ) (hk : k < x0)
    (x : Fin x0 → ℝ) (y : ℝ) :
    saleTime lam f π x0 k (Function.update x ⟨k, hk⟩ y) = saleTime lam f π x0 k x := by
  unfold saleTime
  refine Finset.sum_congr rfl (fun i hi => ?_)
  simp only [Finset.mem_filter] at hi
  have : i ≠ ⟨k, hk⟩ := by intro h; rw [h] at hi; simp at hi
  rw [Function.update_of_ne this]

/-- Pathwise form of the revenue rate. -/
lemma cf_rate_path (lam : ℝ) (f : ℝ → ℝ) (π : ℕ → ℝ) (x0 : ℕ)
    (hlam : 0 < lam) (hf : Assumption1 f) (e : Fin x0 → ℝ) (he : ∀ i, 0 ≤ e i)
    {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (lam * rateRev f π (Xminus lam f π x0 e t)) =
      ∑ k ∈ Finset.Icc 1 x0, (Ioc (saleTime lam f π x0 (k - 1) e) (saleTime lam f π x0 k e)).indicator
        (fun _ => ENNReal.ofReal (π (x0 - k + 1) * (lam * Fbar f (π (x0 - k + 1))))) t := by
  set S := fun j => saleTime lam f π x0 j e with hSdef
  obtain ⟨m, hm, hfil⟩ := cf_filter_Icc (fun j => S j < t)
    (fun j j' hjj h => lt_of_le_of_lt (cf_saleTime_mono lam f π x0 hlam hf e he hjj) h) x0
  have hX : Xminus lam f π x0 e t = x0 - m := by
    unfold Xminus
    have : (Finset.Icc 1 x0).filter (fun k => saleTime lam f π x0 k e < t) =
        Finset.Icc 1 m := hfil
    rw [this, Nat.card_Icc]
    omega
  have hiff : ∀ j, j ≤ x0 → (S j < t ↔ j ≤ m) := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0
      simp only [hSdef, cf_saleTime_zero]
      exact ⟨fun _ => Nat.zero_le _, fun _ => ht⟩
    · have := congrArg (fun s => j ∈ s) hfil
      simp only [Finset.mem_filter, Finset.mem_Icc, eq_iff_iff] at this
      constructor
      · intro h; exact (this.1 ⟨⟨hpos, hj⟩, h⟩).2
      · intro h; exact (this.2 ⟨hpos, h⟩).2
  have hterm : ∀ k ∈ Finset.Icc 1 x0,
      (Ioc (S (k - 1)) (S k)).indicator
        (fun _ => ENNReal.ofReal (π (x0 - k + 1) * (lam * Fbar f (π (x0 - k + 1))))) t =
      if k = m + 1 then ENNReal.ofReal (π (x0 - k + 1) * (lam * Fbar f (π (x0 - k + 1))))
        else 0 := by
    intro k hk
    have hk' := Finset.mem_Icc.1 hk
    have h1 := hiff (k - 1) (by omega)
    have h2 := hiff k hk'.2
    by_cases hkm : k = m + 1
    · rw [if_pos hkm, Set.indicator_of_mem]
      exact ⟨h1.2 (by omega), le_of_not_gt (fun h => by have := h2.1 h; omega)⟩
    · rw [if_neg hkm, Set.indicator_of_notMem]
      rintro ⟨ha, hb⟩
      have h3 := h1.1 ha
      have h4 : k ≤ m := by omega
      exact absurd (h2.2 h4) (not_lt.2 hb)
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
  rw [hX]
  by_cases hmx : m < x0
  · rw [if_pos (Finset.mem_Icc.2 ⟨by omega, by omega⟩)]
    have hidx : x0 - (m + 1) + 1 = x0 - m := by omega
    rw [hidx]
    unfold rateRev
    rw [if_neg (by omega)]
    congr 1; ring
  · have : m = x0 := by omega
    subst this
    rw [if_neg (by simp), Nat.sub_self]
    unfold rateRev
    simp

lemma cf_Fbar_pos' (f : ℝ → ℝ) (hf : Assumption1 f) {p : ℝ} (hp : 0 ≤ p) : 0 < Fbar f p := by
  unfold Fbar
  rw [setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ (fun v => hf.nonnegative v))
    hf.integrable.integrableOn]
  have : Function.support f ∩ Ioi p = Ioi p := by
    ext v
    simp only [mem_inter_iff, Function.mem_support, mem_Ioi]
    constructor
    · exact fun h => h.2
    · intro hv
      exact ⟨(hf.positive_of_nonnegative v (by linarith)).ne', hv⟩
  rw [this, Real.volume_Ioi]
  simp

theorem solution (lam : ℝ) (f : ℝ → ℝ) (π : ℕ → ℝ)
    (x0 : ℕ) (T : ℝ) (hlam : 0 < lam) (hf : Assumption1 f)
    (hπ : ∀ x : ℕ, 1 ≤ x → 0 ≤ π x) (hT : 0 ≤ T) :
    J lam f π x0 T =
      ∫⁻ e, (∫⁻ t in Set.Ioc 0 T,
        ENNReal.ofReal (lam * rateRev f π (Xminus lam f π x0 e t)) ∂volume)
        ∂clockLaw x0 := by
  set S := fun j e => saleTime lam f π x0 j e with hSdef
  have hSm : ∀ j, Measurable (S j) := fun j => cf_saleTime_measurable lam f π x0 j
  set c : ℕ → ℝ := fun k => π (x0 - k + 1) with hcdef
  set μ : ℕ → ℝ := fun k => lam * Fbar f (π (x0 - k + 1)) with hμdef
  have hc : ∀ k ∈ Finset.Icc 1 x0, 0 ≤ c k := by
    intro k hk; have := Finset.mem_Icc.1 hk; exact hπ _ (by omega)
  have hμ : ∀ k ∈ Finset.Icc 1 x0, 0 < μ k := by
    intro k hk
    exact mul_pos hlam (cf_Fbar_pos' f hf (hc k hk))
  set F : ℕ → (Fin x0 → ℝ) → ℝ≥0∞ := fun k e =>
    ENNReal.ofReal (c k) * ENNReal.ofReal (μ k * (min (S k e) T - S (k - 1) e)) with hFdef
  set G : ℕ → (Fin x0 → ℝ) → ℝ≥0∞ := fun k e =>
    if S k e ≤ T then ENNReal.ofReal (c k) else 0 with hGdef
  have hFm : ∀ k, Measurable (F k) := by
    intro k
    have h1 := hSm k
    have h2 := hSm (k - 1)
    simp only [hFdef]
    fun_prop
  have hGm : ∀ k, Measurable (G k) := by
    intro k
    exact Measurable.ite (measurableSet_le (hSm k) measurable_const) measurable_const
      measurable_const
  -- Step 1: pathwise left side
  have hpath : ∀ e : Fin x0 → ℝ, (∀ i, 0 ≤ e i) →
      ∫⁻ t in Set.Ioc 0 T, ENNReal.ofReal (lam * rateRev f π (Xminus lam f π x0 e t)) =
        ∑ k ∈ Finset.Icc 1 x0, F k e := by
    intro e he
    rw [setLIntegral_congr_fun measurableSet_Ioc
      (fun t ht => cf_rate_path lam f π x0 hlam hf e he ht.1)]
    rw [lintegral_finsetSum _ (fun k _ => measurable_const.indicator measurableSet_Ioc)]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [lintegral_indicator_const measurableSet_Ioc,
      Measure.restrict_apply measurableSet_Ioc, Set.Ioc_inter_Ioc,
      max_eq_left (cf_saleTime_nonneg lam f π x0 (k - 1) hlam hf e he), Real.volume_Ioc]
    simp only [hFdef]
    rw [ENNReal.ofReal_mul (hc k hk), ENNReal.ofReal_mul (hμ k hk).le, mul_assoc]
  -- Step 2: right side
  have hrev : ∀ e, ENNReal.ofReal (revenueBy lam f π x0 T e) = ∑ k ∈ Finset.Icc 1 x0, G k e := by
    intro e
    unfold revenueBy
    rw [ENNReal.ofReal_sum_of_nonneg (fun k hk => by
      split_ifs
      · exact hc k hk
      · exact le_rfl)]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [hGdef]
    split_ifs <;> first | rfl | simp
  -- Step 3: termwise identity
  have hexp1 : IsProbabilityMeasure (expMeasure (1:ℝ)) := isProbabilityMeasure_expMeasure one_pos
  have hkey : ∀ k ∈ Finset.Icc 1 x0, ∫⁻ e, F k e ∂clockLaw x0 = ∫⁻ e, G k e ∂clockLaw x0 := by
    intro k hk
    have hk' := Finset.mem_Icc.1 hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hj : j < x0 := by omega
    unfold clockLaw
    refine lintegral_eq_of_lmarginal_eq {(⟨j, hj⟩ : Fin x0)} (hFm _) (hGm _) ?_
    rw [lmarginal_singleton, lmarginal_singleton]
    funext x
    have hupd : ∀ y, S (j + 1) (Function.update x ⟨j, hj⟩ y) =
        S j x + y / μ (j + 1) := by
      intro y
      simp only [hSdef, hμdef]
      rw [cf_saleTime_succ lam f π x0 j hj, cf_saleTime_update lam f π x0 j hj,
        Function.update_self]
      have : x0 - (j + 1) + 1 = x0 - j := by omega
      rw [this]
    have hupd0 : ∀ y, S (j + 1 - 1) (Function.update x ⟨j, hj⟩ y) = S j x := by
      intro y
      simp only [hSdef, Nat.add_sub_cancel]
      exact cf_saleTime_update lam f π x0 j hj x y
    simp only [hFdef, hGdef, hupd, hupd0]
    rw [lintegral_const_mul _ (by fun_prop),
      cf_single_clock (S j x) (μ (j + 1)) T (hμ _ hk)]
    have hset : MeasurableSet {y : ℝ | S j x + y / μ (j + 1) ≤ T} :=
      measurableSet_le (by fun_prop) measurable_const
    rw [← lintegral_indicator_const hset]
    congr 1
  -- Step 4: assemble
  unfold J
  simp_rw [hrev]
  rw [lintegral_finsetSum _ (fun k _ => hGm k), ← Finset.sum_congr rfl hkey,
    ← lintegral_finsetSum _ (fun k _ => hFm k)]
  apply lintegral_congr_ae
  filter_upwards [cf_clock_ae_nonneg x0] with e he
  exact (hpath e he).symm
