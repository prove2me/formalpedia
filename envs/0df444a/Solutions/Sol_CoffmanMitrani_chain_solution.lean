-- Prove2me | solution 1 for CoffmanMitrani.chain_solution
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-12T13:42:34.610468+00:00
-- url     : https://prove2.me/submissions/58094679-acc1-4ca7-863d-9bd9c92e9f58

import Mathlib
import Definitions.Def_CoffmanMitrani_Data_P
import Definitions.Def_CoffmanMitrani_present
import Definitions.Def_CoffmanMitrani_responseTime
import Definitions.Def_CoffmanMitrani_IsPriority
import Definitions.Def_CoffmanMitrani_Achieves
import Definitions.Def_CoffmanMitrani_Data_loadBound
import Definitions.Def_CoffmanMitrani_chain
import Definitions.Def_CoffmanMitrani_Hss
import Definitions.Def_CoffmanMitrani_arrival
import Definitions.Def_CoffmanMitrani_serviceReq
import Definitions.Def_CoffmanMitrani_IsStrategy


set_option autoImplicit false

/-! C2 Wald core (relay 8): `λ · E[min(e, g)] = P(e ≤ g)` for `e ~ Exp(λ)`, `g ≥ 0`.
Per-interarrival identity behind `E N_i[0, ν) = λ_i E ν` for stopping-type times `ν`
(see scratch/bailed/608dae3b.md, "## C2 Wald route (relay 8)"). -/

namespace CM4W
open MeasureTheory ProbabilityTheory Real Set CoffmanMitrani

theorem expMeasure_ae_pos {r : ℝ} (hr : 0 < r) : ∀ᵐ x ∂(expMeasure r), 0 < x := by
  have := isProbabilityMeasure_expMeasure hr
  rw [ae_iff]
  have hset : {x : ℝ | ¬ 0 < x} = Set.Iic 0 := by ext x; simp
  rw [hset, ← ofReal_cdf, cdf_expMeasure_eq hr]
  simp

theorem expMeasure_real_Ioi {r : ℝ} (hr : 0 < r) {t : ℝ} (ht : 0 ≤ t) :
    (expMeasure r).real (Ioi t) = exp (-(r * t)) := by
  have := isProbabilityMeasure_expMeasure hr
  have h1 : (expMeasure r).real (Ioi t) = 1 - (expMeasure r).real (Iic t) := by
    rw [measureReal_def, measureReal_def, ← compl_Iic, prob_compl_eq_one_sub measurableSet_Iic,
      ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]
  rw [h1, ← cdf_eq_real, cdf_expMeasure_eq hr, if_pos ht]
  ring

theorem integral_exp_neg_mul {r : ℝ} (hr : 0 < r) (g : ℝ) :
    r * ∫ t in (0 : ℝ)..g, exp (-(r * t)) = 1 - exp (-(r * g)) := by
  have hd : ∀ x ∈ uIcc (0 : ℝ) g,
      HasDerivAt (fun t => -exp (-(r * t)) / r) (exp (-(r * x))) x := by
    intro x _
    have h3 : HasDerivAt (fun t => -exp (-(r * t)) / r) (-(exp (-(r * x)) * -(r * 1)) / r) x :=
      (((hasDerivAt_id' x).const_mul r).neg.exp.neg).div_const r
    convert h3 using 1
    rw [eq_div_iff hr.ne']
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun t => exp (-(r * t))).intervalIntegrable _ _),
    show -(r * (0 : ℝ)) = 0 by ring, Real.exp_zero]
  field_simp
  ring

/-- **Wald core.** `λ · E[min(e, g)] = 1 - e^{-λ g} = P(e ≤ g)` for `e ~ Exp(λ)`, `g ≥ 0`. -/
theorem exp_min_mean {r : ℝ} (hr : 0 < r) {g : ℝ} (hg : 0 ≤ g) :
    r * ∫ x, min x g ∂(expMeasure r) = 1 - exp (-(r * g)) := by
  have := isProbabilityMeasure_expMeasure hr
  have hpos := expMeasure_ae_pos hr
  have hnn : 0 ≤ᵐ[expMeasure r] fun x => min x g := by
    filter_upwards [hpos] with x hx
    exact le_min hx.le hg
  have hint : Integrable (fun x => min x g) (expMeasure r) := by
    refine Integrable.mono' (integrable_const g)
      ((measurable_id.min measurable_const).aestronglyMeasurable) ?_
    filter_upwards [hpos] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min hx.le hg)]
    exact min_le_right _ _
  rw [hint.integral_eq_integral_meas_lt hnn]
  have hcongr : ∀ t ∈ Ioi (0 : ℝ),
      (expMeasure r).real {a : ℝ | t < min a g} = (Iio g).indicator (fun t => exp (-(r * t))) t := by
    intro t ht
    by_cases htg : t < g
    · rw [indicator_of_mem (show t ∈ Iio g from htg)]
      have hs : {a : ℝ | t < min a g} = Ioi t := by
        ext a; simp only [mem_ofPred_eq, lt_min_iff, mem_Ioi]; exact ⟨fun h => h.1, fun h => ⟨h, htg⟩⟩
      rw [hs, expMeasure_real_Ioi hr (le_of_lt ht)]
    · rw [indicator_of_notMem (show t ∉ Iio g from htg)]
      have hs : {a : ℝ | t < min a g} = ∅ := by
        ext a; simp only [mem_ofPred_eq, lt_min_iff, mem_empty_iff_false, iff_false, not_and]
        intro _; exact htg
      rw [hs, measureReal_empty]
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, setIntegral_indicator measurableSet_Iio,
    Ioi_inter_Iio, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hg,
    integral_exp_neg_mul hr]


theorem exp_min_lintegral {r : ℝ} (hr : 0 < r) {g : ℝ} (hg : 0 ≤ g) :
    ENNReal.ofReal r * ∫⁻ x, ENNReal.ofReal (min x g) ∂(expMeasure r) =
      ENNReal.ofReal (1 - exp (-(r * g))) := by
  have := isProbabilityMeasure_expMeasure hr
  have hpos := expMeasure_ae_pos hr
  have hnn : 0 ≤ᵐ[expMeasure r] fun x => min x g := by
    filter_upwards [hpos] with x hx
    exact le_min hx.le hg
  have hint : Integrable (fun x => min x g) (expMeasure r) := by
    refine Integrable.mono' (integrable_const g)
      ((measurable_id.min measurable_const).aestronglyMeasurable) ?_
    filter_upwards [hpos] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min hx.le hg)]
    exact min_le_right _ _
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, ← ENNReal.ofReal_mul hr.le,
    exp_min_mean hr hg]

theorem expMeasure_Iic {r : ℝ} (hr : 0 < r) {c : ℝ} (hc : 0 ≤ c) :
    expMeasure r (Iic c) = ENNReal.ofReal (1 - exp (-(r * c))) := by
  have := isProbabilityMeasure_expMeasure hr
  rw [← ofReal_cdf, cdf_expMeasure_eq hr, if_pos hc]

section Resample
variable {ι β : Type*} [DecidableEq ι] [MeasurableSpace β] (μ : ι → Measure β)
  [∀ i, IsProbabilityMeasure (μ i)]

theorem measurable_update_pair (j : ι) :
    Measurable (fun p : β × (ι → β) => Function.update p.2 j p.1) := by
  refine measurable_pi_lambda _ (fun i => ?_)
  by_cases h : i = j
  · subst h; simpa using measurable_fst
  · simp only [Function.update_of_ne h]
    exact (measurable_pi_apply i).comp measurable_snd

/-- Resampling one coordinate of an infinite product measure preserves it. -/
theorem infinitePi_resample (j : ι) :
    MeasurePreserving (fun p : β × (ι → β) => Function.update p.2 j p.1)
      ((μ j).prod (Measure.infinitePi μ)) (Measure.infinitePi μ) := by
  refine ⟨measurable_update_pair j, ?_⟩
  refine Measure.eq_infinitePi (μ := μ) (fun s t ht => ?_)
  rw [Measure.map_apply (measurable_update_pair j)
    (MeasurableSet.pi s.countable_toSet (fun i _ => ht i))]
  by_cases hj : j ∈ s
  · have hset : (fun p : β × (ι → β) => Function.update p.2 j p.1) ⁻¹' Set.pi (s : Set ι) t =
        t j ×ˢ Set.pi ((s.erase j : Finset ι) : Set ι) t := by
      ext ⟨x, ω⟩
      simp only [mem_preimage, mem_pi, Finset.mem_coe, mem_prod, Finset.mem_erase]
      constructor
      · intro h
        refine ⟨by simpa using h j hj, fun i hi => ?_⟩
        simpa [Function.update_of_ne hi.1] using h i hi.2
      · rintro ⟨h1, h2⟩ i hi
        by_cases hij : i = j
        · subst hij; simpa using h1
        · simpa [Function.update_of_ne hij] using h2 i ⟨hij, hi⟩
    rw [hset, Measure.prod_prod, Measure.infinitePi_pi (μ := μ) (fun i _ => ht i),
      Finset.mul_prod_erase s (fun i => μ i (t i)) hj]
  · have hset : (fun p : β × (ι → β) => Function.update p.2 j p.1) ⁻¹' Set.pi (s : Set ι) t =
        (univ : Set β) ×ˢ Set.pi (s : Set ι) t := by
      ext ⟨x, ω⟩
      simp only [mem_preimage, mem_pi, Finset.mem_coe, mem_prod, mem_univ, true_and]
      refine forall₂_congr (fun i hi => ?_)
      have hij : i ≠ j := fun h => hj (h ▸ hi)
      rw [Function.update_of_ne hij]
    rw [hset, Measure.prod_prod, measure_univ, one_mul,
      Measure.infinitePi_pi (μ := μ) (fun i _ => ht i)]

end Resample

theorem P_isProb (D : Data) : IsProbabilityMeasure D.P := by
  haveI : ∀ j : Job D.M, IsProbabilityMeasure (expMeasure (D.lam j.1)) :=
    fun j => isProbabilityMeasure_expMeasure (D.lam_pos j.1)
  haveI : ∀ j : Job D.M, IsProbabilityMeasure (expMeasure (D.mu j.1)) :=
    fun j => isProbabilityMeasure_expMeasure (D.mu_pos j.1)
  unfold Data.P
  infer_instance

/-- Resampling the interarrival coordinate `j` of `Omega` preserves `D.P`. -/
theorem P_resampleA (D : Data) (j : Job D.M) :
    MeasurePreserving (fun p : ℝ × Omega D.M => ((Function.update p.2.1 j p.1, p.2.2) : Omega D.M))
      ((expMeasure (D.lam j.1)).prod D.P) D.P := by
  haveI : ∀ j : Job D.M, IsProbabilityMeasure (expMeasure (D.lam j.1)) :=
    fun j => isProbabilityMeasure_expMeasure (D.lam_pos j.1)
  haveI : ∀ j : Job D.M, IsProbabilityMeasure (expMeasure (D.mu j.1)) :=
    fun j => isProbabilityMeasure_expMeasure (D.mu_pos j.1)
  have h1 := infinitePi_resample (fun j : Job D.M => expMeasure (D.lam j.1)) j
  have h2 := MeasurePreserving.symm _ (measurePreserving_prodAssoc (expMeasure (D.lam j.1))
    (Measure.infinitePi fun j : Job D.M => expMeasure (D.lam j.1))
    ((Measure.infinitePi fun j : Job D.M => expMeasure (D.mu j.1)).prod
      (Measure.infinitePi fun _ : Job D.M =>
        Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval))))
  have h3 := (h1.prod (MeasurePreserving.id ((Measure.infinitePi fun j : Job D.M =>
    expMeasure (D.mu j.1)).prod (Measure.infinitePi fun _ : Job D.M =>
        Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval))))).comp h2
  unfold Data.P
  exact h3

/-- **Wald core on `Omega`.** For `g ≥ 0` and `A` not depending on the interarrival
coordinate `j`: `λ E[1_A min(e_j, g)] = P(A ∩ {e_j ≤ g})`. -/
theorem wald_core (D : Data) (j : Job D.M) (g : Omega D.M → ℝ) (A : Set (Omega D.M))
    (hg : Measurable g) (hA : MeasurableSet A) (hg0 : ∀ ω, 0 ≤ g ω)
    (hginv : ∀ (ω : Omega D.M) (x : ℝ), g ((Function.update ω.1 j x, ω.2) : Omega D.M) = g ω)
    (hAinv : ∀ (ω : Omega D.M) (x : ℝ),
      ((Function.update ω.1 j x, ω.2) : Omega D.M) ∈ A ↔ ω ∈ A) :
    ENNReal.ofReal (D.lam j.1) *
        ∫⁻ ω, A.indicator (fun ω => ENNReal.ofReal (min (ω.1 j) (g ω))) ω ∂D.P =
      D.P (A ∩ {ω | ω.1 j ≤ g ω}) := by
  have hr : 0 < D.lam j.1 := D.lam_pos j.1
  have := isProbabilityMeasure_expMeasure hr
  haveI := P_isProb D
  have hmp := P_resampleA D j
  have hL : ∫⁻ ω, A.indicator (fun ω => ENNReal.ofReal (min (ω.1 j) (g ω))) ω ∂D.P =
      ∫⁻ ω, A.indicator (fun ω => ∫⁻ x, ENNReal.ofReal (min x (g ω)) ∂(expMeasure (D.lam j.1)))
        ω ∂D.P := by
    have hmeasF : Measurable (A.indicator
        (fun ω : Omega D.M => ENNReal.ofReal (min (ω.1 j) (g ω)))) :=
      (ENNReal.measurable_ofReal.comp
        (((measurable_pi_apply j).comp measurable_fst).min hg)).indicator hA
    rw [← hmp.lintegral_comp hmeasF]
    have hpt : ∀ p : ℝ × Omega D.M,
        A.indicator (fun ω => ENNReal.ofReal (min (ω.1 j) (g ω)))
          ((Function.update p.2.1 j p.1, p.2.2) : Omega D.M) =
        (Prod.snd ⁻¹' A).indicator
          (fun p : ℝ × Omega D.M => ENNReal.ofReal (min p.1 (g p.2))) p := by
      intro p
      by_cases hp : p.2 ∈ A
      · rw [indicator_of_mem ((hAinv p.2 p.1).2 hp),
          indicator_of_mem (show p ∈ Prod.snd ⁻¹' A from hp), hginv p.2 p.1]
        simp only [Function.update_self]
      · rw [indicator_of_notMem (fun h => hp ((hAinv p.2 p.1).1 h)),
          indicator_of_notMem (show p ∉ Prod.snd ⁻¹' A from hp)]
    have hmeasG : Measurable ((Prod.snd ⁻¹' A).indicator
        (fun p : ℝ × Omega D.M => ENNReal.ofReal (min p.1 (g p.2)))) :=
      (ENNReal.measurable_ofReal.comp
        (measurable_fst.min (hg.comp measurable_snd))).indicator (measurable_snd hA)
    rw [lintegral_congr hpt, lintegral_prod_symm _ hmeasG.aemeasurable]
    refine lintegral_congr (fun ω => ?_)
    by_cases hω : ω ∈ A
    · simp [Set.indicator_apply, hω]
    · simp [Set.indicator_apply, hω]
  have hS : MeasurableSet (A ∩ {ω : Omega D.M | ω.1 j ≤ g ω}) :=
    hA.inter (measurableSet_le ((measurable_pi_apply j).comp measurable_fst) hg)
  have hR : D.P (A ∩ {ω | ω.1 j ≤ g ω}) =
      ∫⁻ ω, A.indicator (fun ω => ENNReal.ofReal (1 - exp (-(D.lam j.1 * g ω)))) ω ∂D.P := by
    rw [← hmp.measure_preimage hS.nullMeasurableSet, Measure.prod_apply_symm (hmp.measurable hS)]
    refine lintegral_congr (fun ω => ?_)
    by_cases hω : ω ∈ A
    · rw [indicator_of_mem hω]
      have hpre : (fun x : ℝ => (x, ω)) ⁻¹' ((fun p : ℝ × Omega D.M =>
          ((Function.update p.2.1 j p.1, p.2.2) : Omega D.M)) ⁻¹'
            (A ∩ {ω | ω.1 j ≤ g ω})) = Iic (g ω) := by
        ext x
        simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq, mem_Iic, hAinv, hginv,
          Function.update_self, hω, true_and]
      rw [hpre, expMeasure_Iic hr (hg0 ω)]
    · rw [indicator_of_notMem hω]
      have hpre : (fun x : ℝ => (x, ω)) ⁻¹' ((fun p : ℝ × Omega D.M =>
          ((Function.update p.2.1 j p.1, p.2.2) : Omega D.M)) ⁻¹'
            (A ∩ {ω | ω.1 j ≤ g ω})) = ∅ := by
        ext x
        simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq, hAinv, hω, false_and,
          mem_empty_iff_false]
      rw [hpre, measure_empty]
  rw [hL, hR, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr (fun ω => ?_)
  by_cases hω : ω ∈ A
  · simp only [indicator_of_mem hω]
    exact exp_min_lintegral hr (hg0 ω)
  · simp only [indicator_of_notMem hω, mul_zero]

/-- **Wald sum (W2 core).** Summing `wald_core` over the class-`i` interarrivals. -/
theorem wald_sum (D : Data) (i : Fin D.M) (g : ℕ → Omega D.M → ℝ) (A : ℕ → Set (Omega D.M))
    (hg : ∀ m, Measurable (g m)) (hA : ∀ m, MeasurableSet (A m)) (hg0 : ∀ m ω, 0 ≤ g m ω)
    (hginv : ∀ m (ω : Omega D.M) (x : ℝ),
      g m ((Function.update ω.1 (i, m) x, ω.2) : Omega D.M) = g m ω)
    (hAinv : ∀ m (ω : Omega D.M) (x : ℝ),
      ((Function.update ω.1 (i, m) x, ω.2) : Omega D.M) ∈ A m ↔ ω ∈ A m) :
    ENNReal.ofReal (D.lam i) *
        ∫⁻ ω, ∑' m, (A m).indicator (fun ω => ENNReal.ofReal (min (ω.1 (i, m)) (g m ω))) ω ∂D.P =
      ∑' m, D.P (A m ∩ {ω | ω.1 (i, m) ≤ g m ω}) := by
  have hmeas : ∀ m, Measurable ((A m).indicator
      (fun ω : Omega D.M => ENNReal.ofReal (min (ω.1 (i, m)) (g m ω)))) := fun m =>
    (ENNReal.measurable_ofReal.comp
      (((measurable_pi_apply (i, m)).comp measurable_fst).min (hg m))).indicator (hA m)
  rw [lintegral_tsum (fun m => (hmeas m).aemeasurable), ← ENNReal.tsum_mul_left]
  exact tsum_congr (fun m => wald_core D (i, m) (g m) (A m) (hg m) (hA m) (hg0 m)
    (hginv m) (hAinv m))

/-- Mean of the exponential law: `r * E[X] = 1`. -/
theorem exp_mean_lintegral {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal r * ∫⁻ x, ENNReal.ofReal x ∂(expMeasure r) = 1 := by
  have := isProbabilityMeasure_expMeasure hr
  have hpos := expMeasure_ae_pos hr
  have h1 : ∫⁻ x, ENNReal.ofReal x ∂(expMeasure r) =
      ∫⁻ x, ⨆ n : ℕ, ENNReal.ofReal (min x n) ∂(expMeasure r) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hpos] with x hx
    refine le_antisymm ?_ (iSup_le fun n => ENNReal.ofReal_le_ofReal (min_le_left _ _))
    obtain ⟨n, hn⟩ := exists_nat_ge x
    calc ENNReal.ofReal x = ENNReal.ofReal (min x n) := by rw [min_eq_left hn]
      _ ≤ ⨆ n : ℕ, ENNReal.ofReal (min x n) := le_iSup (fun n : ℕ => ENNReal.ofReal (min x n)) n
  have hmono : Monotone (fun (n : ℕ) (x : ℝ) => ENNReal.ofReal (min x n)) := by
    intro a b hab x
    exact ENNReal.ofReal_le_ofReal (min_le_min_left _ (Nat.cast_le.2 hab))
  have hmeas : ∀ n : ℕ, Measurable (fun x : ℝ => ENNReal.ofReal (min x n)) := fun n =>
    ENNReal.measurable_ofReal.comp (measurable_id.min measurable_const)
  rw [h1, lintegral_iSup hmeas hmono, ENNReal.mul_iSup]
  have h2 : ∀ n : ℕ, ENNReal.ofReal r * ∫⁻ x, ENNReal.ofReal (min x n) ∂(expMeasure r) =
      ENNReal.ofReal (1 - exp (-(r * n))) := fun n => exp_min_lintegral hr (Nat.cast_nonneg n)
  simp only [h2]
  refine iSup_eq_of_tendsto ?_ ?_
  · intro a b hab
    refine ENNReal.ofReal_le_ofReal ?_
    have : exp (-(r * b)) ≤ exp (-(r * a)) := by
      apply Real.exp_le_exp.2
      have : (a : ℝ) ≤ b := Nat.cast_le.2 hab
      nlinarith
    linarith
  · have ht : Filter.Tendsto (fun n : ℕ => 1 - exp (-(r * n))) Filter.atTop (nhds (1 - 0)) :=
      tendsto_const_nhds.sub (Real.tendsto_exp_atBot.comp
        (Filter.tendsto_neg_atTop_atBot.comp
          (Filter.Tendsto.const_mul_atTop hr tendsto_natCast_atTop_atTop)))
    have := (ENNReal.continuous_ofReal.tendsto _).comp ht
    rw [sub_zero, ENNReal.ofReal_one] at this
    exact this

/-- Resampling the service coordinate `j` of `Omega` preserves `D.P`. -/
theorem P_resampleS (D : Data) (j : Job D.M) :
    MeasurePreserving (fun p : ℝ × Omega D.M =>
        ((p.2.1, Function.update p.2.2.1 j p.1, p.2.2.2) : Omega D.M))
      ((expMeasure (D.mu j.1)).prod D.P) D.P := by
  haveI : ∀ j : Job D.M, IsProbabilityMeasure (expMeasure (D.lam j.1)) :=
    fun j => isProbabilityMeasure_expMeasure (D.lam_pos j.1)
  haveI : ∀ j : Job D.M, IsProbabilityMeasure (expMeasure (D.mu j.1)) :=
    fun j => isProbabilityMeasure_expMeasure (D.mu_pos j.1)
  set E := expMeasure (D.mu j.1)
  set μA := Measure.infinitePi fun j : Job D.M => expMeasure (D.lam j.1)
  set μS := Measure.infinitePi fun j : Job D.M => expMeasure (D.mu j.1)
  set U := Measure.infinitePi fun _ : Job D.M =>
        Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval)
  have h1 := infinitePi_resample (fun j : Job D.M => expMeasure (D.mu j.1)) j
  have hd := (h1.prod (MeasurePreserving.id U)).comp
    (MeasurePreserving.symm _ (measurePreserving_prodAssoc E μS U))
  have ha := MeasurePreserving.symm _ (measurePreserving_prodAssoc E μA (μS.prod U))
  have hb := (Measure.measurePreserving_swap (μ := E) (ν := μA)).prod
    (MeasurePreserving.id (μS.prod U))
  have hc := measurePreserving_prodAssoc μA E (μS.prod U)
  have hall := ((((MeasurePreserving.id μA).prod hd).comp hc).comp hb).comp ha
  unfold Data.P
  exact hall

/-- **Service-mean core.** For `B` not depending on the service coordinate `j`:
`μ E[1_B X_j] = P(B)`. -/
theorem service_core (D : Data) (j : Job D.M) (B : Set (Omega D.M)) (hB : MeasurableSet B)
    (hBinv : ∀ (ω : Omega D.M) (x : ℝ),
      ((ω.1, Function.update ω.2.1 j x, ω.2.2) : Omega D.M) ∈ B ↔ ω ∈ B) :
    ENNReal.ofReal (D.mu j.1) *
        ∫⁻ ω, B.indicator (fun ω => ENNReal.ofReal (ω.2.1 j)) ω ∂D.P = D.P B := by
  have hr : 0 < D.mu j.1 := D.mu_pos j.1
  have := isProbabilityMeasure_expMeasure hr
  haveI := P_isProb D
  have hmp := P_resampleS D j
  have hmeasF : Measurable (B.indicator (fun ω : Omega D.M => ENNReal.ofReal (ω.2.1 j))) :=
    (ENNReal.measurable_ofReal.comp
      ((measurable_pi_apply j).comp (measurable_fst.comp measurable_snd))).indicator hB
  rw [← hmp.lintegral_comp hmeasF]
  have hpt : ∀ p : ℝ × Omega D.M,
      B.indicator (fun ω => ENNReal.ofReal (ω.2.1 j))
        ((p.2.1, Function.update p.2.2.1 j p.1, p.2.2.2) : Omega D.M) =
      (Prod.snd ⁻¹' B).indicator (fun p : ℝ × Omega D.M => ENNReal.ofReal p.1) p := by
    intro p
    by_cases hp : p.2 ∈ B
    · rw [indicator_of_mem ((hBinv p.2 p.1).2 hp),
        indicator_of_mem (show p ∈ Prod.snd ⁻¹' B from hp)]
      simp only [Function.update_self]
    · rw [indicator_of_notMem (fun h => hp ((hBinv p.2 p.1).1 h)),
        indicator_of_notMem (show p ∉ Prod.snd ⁻¹' B from hp)]
  have hmeasG : Measurable ((Prod.snd ⁻¹' B).indicator
      (fun p : ℝ × Omega D.M => ENNReal.ofReal p.1)) :=
    (ENNReal.measurable_ofReal.comp measurable_fst).indicator (measurable_snd hB)
  rw [lintegral_congr hpt, lintegral_prod_symm _ hmeasG.aemeasurable,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_indicator_one hB]
  refine lintegral_congr (fun ω => ?_)
  by_cases hω : ω ∈ B
  · have hin : ∀ x : ℝ, (Prod.snd ⁻¹' B).indicator
        (fun p : ℝ × Omega D.M => ENNReal.ofReal p.1) (x, ω) = ENNReal.ofReal x :=
      fun x => indicator_of_mem (show (x, ω) ∈ Prod.snd ⁻¹' B from hω) _
    simp only [hin, indicator_of_mem hω, Pi.one_apply]
    exact exp_mean_lintegral hr
  · have hin : ∀ x : ℝ, (Prod.snd ⁻¹' B).indicator
        (fun p : ℝ × Omega D.M => ENNReal.ofReal p.1) (x, ω) = 0 :=
      fun x => indicator_of_notMem (show (x, ω) ∉ Prod.snd ⁻¹' B from hω) _
    simp only [hin, lintegral_zero, mul_zero, indicator_of_notMem hω]

/-- Deterministic telescoping behind W2: truncated interarrivals sum to `min (S N) ν`. -/
theorem telescope_min (e : ℕ → ℝ) (he : ∀ k, 0 ≤ e k) {ν : ℝ} (hν : 0 ≤ ν) (N : ℕ) :
    ∑ m ∈ Finset.range N, (if ∑ k ∈ Finset.range m, e k ≤ ν then
        min (e m) (ν - ∑ k ∈ Finset.range m, e k) else 0) =
      min (∑ k ∈ Finset.range N, e k) ν := by
  induction N with
  | zero => simp [min_eq_left hν]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    split_ifs with h
    · rw [min_eq_left h]
      rcases le_total (e N) (ν - ∑ k ∈ Finset.range N, e k) with h2 | h2
      · rw [min_eq_left h2, min_eq_left (by linarith)]
      · rw [min_eq_right h2, min_eq_right (by linarith)]
        ring
    · rw [not_le] at h
      rw [min_eq_right h.le, add_zero, min_eq_right (by linarith [he N])]

/-- `ν = Σ_m 1{S_m ≤ ν} min(e_m, ν - S_m)` once the partial sums pass `ν`. -/
theorem telescope_tsum (e : ℕ → ℝ) (he : ∀ k, 0 ≤ e k) {ν : ℝ} (hν : 0 ≤ ν)
    (hfin : ∃ N, ν < ∑ k ∈ Finset.range N, e k) :
    ∑' m, ENNReal.ofReal (if ∑ k ∈ Finset.range m, e k ≤ ν then
        min (e m) (ν - ∑ k ∈ Finset.range m, e k) else 0) = ENNReal.ofReal ν := by
  obtain ⟨N, hN⟩ := hfin
  have hz : ∀ m ∉ Finset.range N, ENNReal.ofReal (if ∑ k ∈ Finset.range m, e k ≤ ν then
      min (e m) (ν - ∑ k ∈ Finset.range m, e k) else 0) = 0 := by
    intro m hm
    have hNm : N ≤ m := not_lt.1 (Finset.mem_range.not.1 hm)
    have : ∑ k ∈ Finset.range N, e k ≤ ∑ k ∈ Finset.range m, e k :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hNm) (fun k _ _ => he k)
    rw [if_neg (by linarith), ENNReal.ofReal_zero]
  have hnn : ∀ m ∈ Finset.range N, 0 ≤ (if ∑ k ∈ Finset.range m, e k ≤ ν then
      min (e m) (ν - ∑ k ∈ Finset.range m, e k) else 0) := by
    intro m _
    split_ifs with h
    · exact le_min (he m) (by linarith)
    · exact le_rfl
  rw [tsum_eq_sum hz, ← ENNReal.ofReal_sum_of_nonneg hnn, telescope_min e he hν N,
    min_eq_right hN.le]


/-! ### Relay 10: Wald for stopping-type times (W2 general form) -/

/-- Atomless resampling: `P(e_j = g) = 0` when `g` does not see coordinate `j`. -/
theorem P_eq_null (D : Data) (j : Job D.M) (g : Omega D.M → ℝ) (hg : Measurable g)
    (hginv : ∀ (ω : Omega D.M) (x : ℝ), g ((Function.update ω.1 j x, ω.2) : Omega D.M) = g ω) :
    D.P {ω | ω.1 j = g ω} = 0 := by
  have hr : 0 < D.lam j.1 := D.lam_pos j.1
  have := isProbabilityMeasure_expMeasure hr
  haveI := P_isProb D
  have hmp := P_resampleA D j
  have hS : MeasurableSet {ω : Omega D.M | ω.1 j = g ω} :=
    measurableSet_eq_fun ((measurable_pi_apply j).comp measurable_fst) hg
  rw [← hmp.measure_preimage hS.nullMeasurableSet, Measure.prod_apply_symm (hmp.measurable hS)]
  have hac : expMeasure (D.lam j.1) ≪ volume := by
    unfold expMeasure gammaMeasure
    exact withDensity_absolutelyContinuous _ _
  have hpt : ∀ ω : Omega D.M, expMeasure (D.lam j.1) ((fun x : ℝ => (x, ω)) ⁻¹'
      ((fun p : ℝ × Omega D.M => ((Function.update p.2.1 j p.1, p.2.2) : Omega D.M)) ⁻¹'
        {ω | ω.1 j = g ω})) = 0 := by
    intro ω
    have hpre : (fun x : ℝ => (x, ω)) ⁻¹'
        ((fun p : ℝ × Omega D.M => ((Function.update p.2.1 j p.1, p.2.2) : Omega D.M)) ⁻¹'
          {ω | ω.1 j = g ω}) = {g ω} := by
      ext x
      simp only [mem_preimage, mem_setOf_eq, Function.update_self, hginv, mem_singleton_iff]
    rw [hpre]
    exact hac (Real.volume_singleton)
  simp only [hpt, lintegral_zero]

/-- Class-`i` "not yet stopped before index `m`" event. -/
def Aset (D : Data) (i : Fin D.M) (g : ℕ → Omega D.M → ℝ) (m : ℕ) : Set (Omega D.M) :=
  {ω | ∀ j < m, ω.1 (i, j) < g j ω}

theorem Aset_meas (D : Data) (i : Fin D.M) (g : ℕ → Omega D.M → ℝ) (hg : ∀ m, Measurable (g m))
    (m : ℕ) : MeasurableSet (Aset D i g m) := by
  have : Aset D i g m = ⋂ j ∈ Finset.range m, {ω : Omega D.M | ω.1 (i, j) < g j ω} := by
    ext ω; simp [Aset]
  rw [this]
  exact Finset.measurableSet_biInter _
    (fun j _ => measurableSet_lt ((measurable_pi_apply _).comp measurable_fst) (hg j))

theorem Aset_inv (D : Data) (i : Fin D.M) (g : ℕ → Omega D.M → ℝ)
    (hginv : ∀ j m (ω : Omega D.M) (x : ℝ), j ≤ m →
      g j ((Function.update ω.1 (i, m) x, ω.2) : Omega D.M) = g j ω)
    (m : ℕ) (ω : Omega D.M) (x : ℝ) :
    ((Function.update ω.1 (i, m) x, ω.2) : Omega D.M) ∈ Aset D i g m ↔ ω ∈ Aset D i g m := by
  simp only [Aset, mem_setOf_eq]
  refine forall_congr' (fun j => imp_congr_right (fun hj => ?_))
  have hne : (i, j) ≠ (i, m) := fun h => by
    simp only [Prod.mk.injEq, true_and] at h
    omega
  rw [Function.update_of_ne hne, hginv j m ω x hj.le]

/-- **Wald for stopping-type times.** `g j` sees only class-`i` interarrivals of index `< j`
(plus anything else); if the truncated sums telescope to `ν` and the stopped event is
`{arrival (i, m) < ν}`, then `λ_i E ν = Σ_m P(arrival (i, m) < ν)` (all in `[0, ∞]`). -/
theorem wald_count (D : Data) (i : Fin D.M) (g : ℕ → Omega D.M → ℝ) (ν : Omega D.M → ℝ)
    (hg : ∀ m, Measurable (g m)) (hg0 : ∀ m ω, 0 ≤ g m ω)
    (hginv : ∀ j m (ω : Omega D.M) (x : ℝ), j ≤ m →
      g j ((Function.update ω.1 (i, m) x, ω.2) : Omega D.M) = g j ω)
    (hsum : ∀ᵐ ω ∂D.P, ∑' m, (Aset D i g m).indicator
        (fun ω => ENNReal.ofReal (min (ω.1 (i, m)) (g m ω))) ω = ENNReal.ofReal (ν ω))
    (hcnt : ∀ m, ∀ᵐ ω ∂D.P, (ω ∈ Aset D i g (m + 1) ↔ ∑ k ∈ Finset.range (m + 1), ω.1 (i, k) < ν ω)) :
    ENNReal.ofReal (D.lam i) * ∫⁻ ω, ENNReal.ofReal (ν ω) ∂D.P =
      ∑' m, D.P {ω | ∑ k ∈ Finset.range (m + 1), ω.1 (i, k) < ν ω} := by
  rw [← lintegral_congr_ae hsum, wald_sum D i g (Aset D i g) hg (Aset_meas D i g hg) hg0
    (fun m ω x => hginv m m ω x le_rfl) (Aset_inv D i g hginv)]
  refine tsum_congr (fun m => ?_)
  have hnull : ∀ᵐ ω ∂D.P, ω.1 (i, m) ≠ g m ω := by
    rw [ae_iff]
    simpa using P_eq_null D (i, m) (g m) (hg m) (fun ω x => hginv m m ω x le_rfl)
  have h1 : (Aset D i g m ∩ {ω | ω.1 (i, m) ≤ g m ω} : Set (Omega D.M)) =ᵐ[D.P]
      Aset D i g (m + 1) := by
    refine hnull.mono fun ω h => propext ?_
    show ω ∈ Aset D i g m ∩ {ω | ω.1 (i, m) ≤ g m ω} ↔ ω ∈ Aset D i g (m + 1)
    simp only [Aset, mem_inter_iff, mem_setOf_eq]
    constructor
    · rintro ⟨hA, hle⟩ j hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact hA j hj
      · exact lt_of_le_of_ne hle h
    · intro hA
      exact ⟨fun j hj => hA j (Nat.lt_succ_of_lt hj), (hA m (Nat.lt_succ_self m)).le⟩
  rw [measure_congr h1]
  exact measure_congr ((hcnt m).mono fun ω h => propext h)

/-- Deterministic stopping structure: deadlines `Dl j` (nondecreasing, `Dl 0 ≥ 0`), partial sums
`S j = Σ_{k<j} e k`, stop at the first `L` with `S (L+1) ≥ Dl L`. With `g j = max 0 (Dl j - S j)`
the truncated interarrivals telescope to `Dl L`. -/
theorem stop_sum (e Dl : ℕ → ℝ) (he : ∀ k, 0 ≤ e k) (hD : Monotone Dl) (hD0 : 0 ≤ Dl 0) (L : ℕ)
    (hL : ∀ j < L, ∑ k ∈ Finset.range (j + 1), e k < Dl j)
    (hLs : Dl L ≤ ∑ k ∈ Finset.range (L + 1), e k) :
    ∑' m, {m : ℕ | ∀ j < m, e j < max 0 (Dl j - ∑ k ∈ Finset.range j, e k)}.indicator
        (fun m => ENNReal.ofReal (min (e m) (max 0 (Dl m - ∑ k ∈ Finset.range m, e k)))) m =
      ENNReal.ofReal (Dl L) := by
  have hSs : ∀ j, ∑ k ∈ Finset.range (j + 1), e k = ∑ k ∈ Finset.range j, e k + e j :=
    fun j => Finset.sum_range_succ e j
  have hlt : ∀ j < L, e j < max 0 (Dl j - ∑ k ∈ Finset.range j, e k) := by
    intro j hj
    have := hL j hj
    rw [hSs] at this
    exact lt_max_of_lt_right (by linarith)
  have hSL : ∑ k ∈ Finset.range L, e k ≤ Dl L := by
    rcases Nat.eq_zero_or_pos L with h0 | hpos
    · subst h0; simp [hD0]
    · obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
      have h1 := hL L' (Nat.lt_succ_self L')
      have h2 := hD (Nat.le_succ L')
      exact (le_of_lt h1).trans h2
  have hgL : max 0 (Dl L - ∑ k ∈ Finset.range L, e k) = Dl L - ∑ k ∈ Finset.range L, e k :=
    max_eq_right (by linarith)
  have hstop : ¬ e L < max 0 (Dl L - ∑ k ∈ Finset.range L, e k) := by
    rw [hgL]
    have := hLs
    rw [hSs] at this
    linarith
  have hz : ∀ m ∉ Finset.range (L + 1),
      {m : ℕ | ∀ j < m, e j < max 0 (Dl j - ∑ k ∈ Finset.range j, e k)}.indicator
        (fun m => ENNReal.ofReal (min (e m) (max 0 (Dl m - ∑ k ∈ Finset.range m, e k)))) m
        = 0 := by
    intro m hm
    have hLm : L < m := by simp only [Finset.mem_range, not_lt] at hm; omega
    exact indicator_of_notMem (by simp only [mem_setOf_eq]; exact fun h => hstop (h L hLm)) _
  rw [tsum_eq_sum hz, Finset.sum_range_succ,
    indicator_of_mem (show L ∈ {m : ℕ | ∀ j < m, e j <
      max 0 (Dl j - ∑ k ∈ Finset.range j, e k)} from hlt), min_eq_right (not_lt.1 hstop)]
  have hmid : ∀ m ∈ Finset.range L,
      {m : ℕ | ∀ j < m, e j < max 0 (Dl j - ∑ k ∈ Finset.range j, e k)}.indicator
        (fun m => ENNReal.ofReal (min (e m) (max 0 (Dl m - ∑ k ∈ Finset.range m, e k)))) m
        = ENNReal.ofReal (e m) := by
    intro m hm
    have hmL : m < L := Finset.mem_range.1 hm
    rw [indicator_of_mem (show m ∈ {m : ℕ | ∀ j < m, e j <
      max 0 (Dl j - ∑ k ∈ Finset.range j, e k)} from fun j hj => hlt j (hj.trans hmL)),
      min_eq_left (hlt m hmL).le]
  rw [Finset.sum_congr rfl hmid, ← ENNReal.ofReal_sum_of_nonneg (fun m _ => he m),
    ← ENNReal.ofReal_add (Finset.sum_nonneg fun m _ => he m) (le_max_left _ _), hgL]
  congr 1
  ring

/-- Same structure: the not-yet-stopped event at `m + 1` is `{S (m+1) < Dl L}`. -/
theorem stop_cnt (e Dl : ℕ → ℝ) (he : ∀ k, 0 ≤ e k) (hD : Monotone Dl) (L : ℕ)
    (hL : ∀ j < L, ∑ k ∈ Finset.range (j + 1), e k < Dl j)
    (hLs : Dl L ≤ ∑ k ∈ Finset.range (L + 1), e k) (m : ℕ) :
    (∀ j < m + 1, e j < max 0 (Dl j - ∑ k ∈ Finset.range j, e k)) ↔
      ∑ k ∈ Finset.range (m + 1), e k < Dl L := by
  have hmono : ∀ a b, a ≤ b → ∑ k ∈ Finset.range a, e k ≤ ∑ k ∈ Finset.range b, e k :=
    fun a b hab => Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab)
      (fun k _ _ => he k)
  have hstep : ∀ j, e j < max 0 (Dl j - ∑ k ∈ Finset.range j, e k) ↔
      ∑ k ∈ Finset.range (j + 1), e k < Dl j := by
    intro j
    rw [Finset.sum_range_succ]
    constructor
    · intro h
      rcases le_total (Dl j - ∑ k ∈ Finset.range j, e k) 0 with h0 | h0
      · rw [max_eq_left h0] at h; linarith [he j]
      · rw [max_eq_right h0] at h; linarith
    · intro h
      exact lt_max_of_lt_right (by linarith)
  simp only [hstep]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have hmL : m < L := by
      by_contra hml
      push Not at hml
      exact absurd (h L (Nat.lt_succ_of_le hml)) (not_lt.2 hLs)
    exact absurd (h m (Nat.lt_succ_self m)) (not_lt.2 ((hD hmL.le).trans hc))
  · intro h j hj
    have hjL : j < L := by
      by_contra hjl
      push Not at hjl
      have := hmono (L + 1) (m + 1) (by omega)
      linarith
    exact (hL j hjL)

/-- **Wald for a time that ignores class `i`** (e.g. `ν = T`, the `n`-th class-`σ k` arrival,
`i ≠ σ k`): `λ_i E ν = Σ_m P(arrival (i, m) < ν)`. -/
theorem wald_fixed (D : Data) (i : Fin D.M) (ν : Omega D.M → ℝ) (hν : Measurable ν)
    (hν0 : ∀ ω, 0 ≤ ν ω)
    (hνinv : ∀ m (ω : Omega D.M) (x : ℝ), ν ((Function.update ω.1 (i, m) x, ω.2) : Omega D.M) = ν ω)
    (hpos : ∀ᵐ ω ∂D.P, ∀ k, 0 ≤ ω.1 (i, k))
    (hfin : ∀ᵐ ω ∂D.P, ∃ N, ν ω ≤ ∑ k ∈ Finset.range (N + 1), ω.1 (i, k)) :
    ENNReal.ofReal (D.lam i) * ∫⁻ ω, ENNReal.ofReal (ν ω) ∂D.P =
      ∑' m, D.P {ω | ∑ k ∈ Finset.range (m + 1), ω.1 (i, k) < ν ω} := by
  classical
  have hmS : ∀ j, Measurable (fun ω : Omega D.M => ∑ k ∈ Finset.range j, ω.1 (i, k)) :=
    fun j => Finset.measurable_sum _ (fun k _ => (measurable_pi_apply _).comp measurable_fst)
  refine wald_count D i (fun j ω => max 0 (ν ω - ∑ k ∈ Finset.range j, ω.1 (i, k))) ν
    (fun j => measurable_const.max (hν.sub (hmS j))) (fun j ω => le_max_left _ _) ?_ ?_ ?_
  · intro j m ω x hjm
    simp only [hνinv]
    congr 2
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hne : (i, k) ≠ (i, m) := fun h => by
      simp only [Prod.mk.injEq, true_and] at h
      have := Finset.mem_range.1 hk
      omega
    exact Function.update_of_ne hne _ _
  · filter_upwards [hpos, hfin] with ω hp hf
    have hL := Nat.find_spec hf
    have hmin : ∀ j < Nat.find hf, ∑ k ∈ Finset.range (j + 1), ω.1 (i, k) < (fun _ => ν ω) j :=
      fun j hj => not_le.1 (Nat.find_min hf hj)
    have key := stop_sum (fun k => ω.1 (i, k)) (fun _ => ν ω) hp (monotone_const) (hν0 ω)
      (Nat.find hf) hmin hL
    rw [← key]
    refine tsum_congr (fun m => ?_)
    by_cases h : ∀ j < m, ω.1 (i, j) < max 0 (ν ω - ∑ k ∈ Finset.range j, ω.1 (i, k))
    · rw [indicator_of_mem (show ω ∈ Aset D i (fun j ω => max 0 (ν ω - ∑ k ∈ Finset.range j, ω.1 (i, k))) m from h),
        indicator_of_mem (show m ∈ {m : ℕ | ∀ j < m, ω.1 (i, j) <
          max 0 (ν ω - ∑ k ∈ Finset.range j, ω.1 (i, k))} from h)]
    · rw [indicator_of_notMem (show ω ∉ Aset D i (fun j ω => max 0 (ν ω - ∑ k ∈ Finset.range j, ω.1 (i, k))) m from h),
        indicator_of_notMem (show m ∉ {m : ℕ | ∀ j < m, ω.1 (i, j) <
          max 0 (ν ω - ∑ k ∈ Finset.range j, ω.1 (i, k))} from h)]
  · intro m
    filter_upwards [hpos, hfin] with ω hp hf
    have hL := Nat.find_spec hf
    have hmin : ∀ j < Nat.find hf, ∑ k ∈ Finset.range (j + 1), ω.1 (i, k) < (fun _ => ν ω) j :=
      fun j hj => not_le.1 (Nat.find_min hf hj)
    exact stop_cnt (fun k => ω.1 (i, k)) (fun _ => ν ω) hp monotone_const (Nat.find hf) hmin hL m

/-- W2 at `ν = T⁺`, `T = arrival (c, n)` of another class `c ≠ i`:
`λ_i E T⁺ = Σ_m P(arrival (i, m) < T⁺)`. -/
theorem wald_arrival (D : Data) (i c : Fin D.M) (hic : i ≠ c) (n : ℕ)
    (hpos : ∀ᵐ ω ∂D.P, ∀ k, 0 ≤ ω.1 (i, k))
    (hfin : ∀ᵐ ω ∂D.P, ∃ N, max 0 (∑ k ∈ Finset.range (n + 1), ω.1 (c, k)) ≤
      ∑ k ∈ Finset.range (N + 1), ω.1 (i, k)) :
    ENNReal.ofReal (D.lam i) *
        ∫⁻ ω, ENNReal.ofReal (max 0 (∑ k ∈ Finset.range (n + 1), ω.1 (c, k))) ∂D.P =
      ∑' m, D.P {ω | ∑ k ∈ Finset.range (m + 1), ω.1 (i, k) <
        max 0 (∑ k ∈ Finset.range (n + 1), ω.1 (c, k))} := by
  have hmS : Measurable (fun ω : Omega D.M => ∑ k ∈ Finset.range (n + 1), ω.1 (c, k)) :=
    Finset.measurable_sum _ (fun k _ => (measurable_pi_apply _).comp measurable_fst)
  refine wald_fixed D i (fun ω => max 0 (∑ k ∈ Finset.range (n + 1), ω.1 (c, k)))
    (measurable_const.max hmS)
    (fun ω => le_max_left _ _) ?_ hpos hfin
  intro m ω x
  show max 0 (∑ k ∈ Finset.range (n + 1), (Function.update ω.1 (i, m) x) (c, k)) =
    max 0 (∑ k ∈ Finset.range (n + 1), ω.1 (c, k))
  rw [Finset.sum_congr rfl (fun k _ =>
    Function.update_of_ne (fun h => hic (Prod.mk.inj h).1.symm) x ω.1)]

end CM4W

set_option autoImplicit false

/-! 608dae3b relay 11: capped busy period `bpc` (abstract, order-theoretic).
`bpc x c w = inf {u ≥ 0 | x + w u ≤ u ∨ c ≤ u}`: always a real (no junk `sInf ∅`), attained for
monotone `w`, monotone in `x` and `w`, local, and satisfies the W4 bound `bpc ≤ x + w bpc`. -/

namespace CM4B
open Set

/-- The capped busy-period set. -/
def bpS (x c : ℝ) (w : ℝ → ℝ) : Set ℝ := {u : ℝ | 0 ≤ u ∧ (x + w u ≤ u ∨ c ≤ u)}

/-- Capped busy period started by work `x` with arrival-work function `w`, capped at `c`. -/
noncomputable def bpc (x c : ℝ) (w : ℝ → ℝ) : ℝ := sInf (bpS x c w)

theorem bpS_bdd (x c : ℝ) (w : ℝ → ℝ) : BddBelow (bpS x c w) := ⟨0, fun _ hu => hu.1⟩

theorem c_mem_bpS {x c : ℝ} (w : ℝ → ℝ) (hc : 0 ≤ c) : c ∈ bpS x c w := ⟨hc, Or.inr le_rfl⟩

theorem bpc_nonneg {x c : ℝ} (w : ℝ → ℝ) (hc : 0 ≤ c) : 0 ≤ bpc x c w :=
  le_csInf ⟨c, c_mem_bpS w hc⟩ (fun _ hu => hu.1)

theorem bpc_le_of_mem {x c u : ℝ} {w : ℝ → ℝ} (hu : u ∈ bpS x c w) : bpc x c w ≤ u :=
  csInf_le (bpS_bdd x c w) hu

theorem bpc_le_c {x c : ℝ} (w : ℝ → ℝ) (hc : 0 ≤ c) : bpc x c w ≤ c :=
  bpc_le_of_mem (c_mem_bpS w hc)

theorem lt_bpc {x c u : ℝ} {w : ℝ → ℝ} (hu0 : 0 ≤ u) (hu : u < bpc x c w) :
    u < x + w u ∧ u < c := by
  have h := notMem_of_lt_csInf hu (bpS_bdd x c w)
  simp only [bpS, mem_setOf_eq, not_and, not_or, not_le] at h
  exact h hu0

/-- The infimum is attained when `w` is monotone (only right limits matter and `w` is monotone). -/
theorem bpc_mem {x c : ℝ} {w : ℝ → ℝ} (hc : 0 ≤ c) (hw : Monotone w) :
    bpc x c w ∈ bpS x c w := by
  set u0 := bpc x c w with hu0
  refine ⟨bpc_nonneg w hc, ?_⟩
  by_cases hcu : c ≤ u0
  · exact Or.inr hcu
  left
  push Not at hcu
  refine le_of_forall_pos_lt_add (fun ε hε => ?_)
  have hε' : 0 < min ε (c - u0) := lt_min hε (by linarith)
  obtain ⟨u, hu, hlt⟩ := exists_lt_of_csInf_lt ⟨c, c_mem_bpS w hc⟩
    (show sInf (bpS x c w) < u0 + min ε (c - u0) from by
      show bpc x c w < u0 + min ε (c - u0)
      linarith)
  have hle : u0 ≤ u := bpc_le_of_mem hu
  rcases hu.2 with h | h
  · have := hw hle
    linarith [min_le_left ε (c - u0)]
  · linarith [min_le_right ε (c - u0)]

theorem bpc_le_iff {x c v : ℝ} {w : ℝ → ℝ} (hc : 0 ≤ c) (hw : Monotone w) :
    bpc x c w ≤ v ↔ ∃ u ∈ bpS x c w, u ≤ v :=
  ⟨fun h => ⟨_, bpc_mem hc hw, h⟩, fun ⟨_, hu, huv⟩ => (bpc_le_of_mem hu).trans huv⟩

/-- Monotone in the start work and the arrival work. -/
theorem bpc_mono {x x' c : ℝ} {w w' : ℝ → ℝ} (hc : 0 ≤ c) (hx : x ≤ x') (hww : ∀ u, w u ≤ w' u) :
    bpc x c w ≤ bpc x' c w' := by
  refine csInf_le_csInf (bpS_bdd x c w) ⟨c, c_mem_bpS w' hc⟩ (fun u hu => ⟨hu.1, ?_⟩)
  rcases hu.2 with h | h
  · exact Or.inl (by linarith [hww u])
  · exact Or.inr h

theorem bpc_mono_c {x c c' : ℝ} {w : ℝ → ℝ} (hc : 0 ≤ c) (hcc : c ≤ c') :
    bpc x c w ≤ bpc x c' w := by
  refine csInf_le_csInf (bpS_bdd x c w) ⟨c', c_mem_bpS w (hc.trans hcc)⟩ (fun u hu => ⟨hu.1, ?_⟩)
  rcases hu.2 with h | h
  · exact Or.inl h
  · exact Or.inr (hcc.trans h)

/-- Locality: a larger arrival-work function that agrees with `w` at the busy period end
gives the same busy period. -/
theorem bpc_local {x c : ℝ} {w w' : ℝ → ℝ} (hc : 0 ≤ c) (hw : Monotone w)
    (hww : ∀ u, w u ≤ w' u) (heq : w' (bpc x c w) = w (bpc x c w)) :
    bpc x c w' = bpc x c w := by
  refine le_antisymm (bpc_le_of_mem ?_) (bpc_mono hc le_rfl hww)
  obtain ⟨h0, h⟩ := bpc_mem (x := x) hc hw
  refine ⟨h0, ?_⟩
  rw [heq]
  exact h

/-- **W4 bound**: the busy period never exceeds start work plus arrived work. -/
theorem bpc_le_add {x c : ℝ} {w : ℝ → ℝ} (hc : 0 ≤ c) (hx : 0 ≤ x) (hw0 : ∀ u, 0 ≤ w u)
    (hw : Monotone w) : bpc x c w ≤ x + w (bpc x c w) := by
  set u0 := bpc x c w
  refine le_of_forall_lt (fun u hu => ?_)
  rcases lt_or_ge u 0 with h | h
  · linarith [hw0 u0]
  · have := (lt_bpc h hu).1
    have := hw hu.le
    linarith

/-- Below the cap the busy period equals start work plus arrived work. -/
theorem bpc_eq_of_lt {x c : ℝ} {w : ℝ → ℝ} (hc : 0 ≤ c) (hx : 0 ≤ x) (hw0 : ∀ u, 0 ≤ w u)
    (hw : Monotone w) (hlt : bpc x c w < c) : bpc x c w = x + w (bpc x c w) := by
  refine le_antisymm (bpc_le_add hc hx hw0 hw) ?_
  rcases (bpc_mem (x := x) hc hw).2 with h | h
  · exact h
  · exact absurd hlt (not_lt.2 h)

/-- Large caps recover the uncapped busy period (`delayBP`-style `sInf`). -/
theorem bpc_eq_sInf {x c : ℝ} {w : ℝ → ℝ} (hc : 0 ≤ c) (hw : Monotone w)
    (hne : ({u : ℝ | 0 ≤ u ∧ x + w u ≤ u}).Nonempty)
    (hcl : sInf {u : ℝ | 0 ≤ u ∧ x + w u ≤ u} ≤ c) :
    bpc x c w = sInf {u : ℝ | 0 ≤ u ∧ x + w u ≤ u} := by
  have hbdd : BddBelow {u : ℝ | 0 ≤ u ∧ x + w u ≤ u} := ⟨0, fun _ hu => hu.1⟩
  refine le_antisymm ?_ ?_
  · -- the uncapped infimum lies in the capped set
    set s := sInf {u : ℝ | 0 ≤ u ∧ x + w u ≤ u}
    have hs0 : 0 ≤ s := le_csInf hne (fun _ hu => hu.1)
    by_cases hsc : s = c
    · exact bpc_le_of_mem ⟨hs0, Or.inr hsc.ge⟩
    have hsc' : s < c := lt_of_le_of_ne hcl hsc
    have hmem : x + w s ≤ s := by
      refine le_of_forall_pos_lt_add (fun ε hε => ?_)
      obtain ⟨u, hu, hlt⟩ := exists_lt_of_csInf_lt hne (show s < s + ε by linarith)
      have := hw (csInf_le hbdd hu)
      linarith [hu.2]
    exact bpc_le_of_mem ⟨hs0, Or.inl hmem⟩
  · show _ ≤ sInf (bpS x c w)
    refine le_csInf ⟨_, bpc_mem (x := x) hc hw⟩ ?_
    intro u hu
    rcases hu.2 with h | h
    · exact csInf_le hbdd ⟨hu.1, h⟩
    · exact hcl.trans h

namespace CM4T
open Set CoffmanMitrani CM4B

/-- Work of jobs satisfying `A` arriving in `[s, t)` (`workG ω g = workA ω (· .1 ∈ g)`). -/
noncomputable def workA {M : ℕ} (ω : Omega M) (A : Job M → Prop) (s t : ℝ) : ℝ :=
  ∑' j : Job M, Set.indicator {j : Job M | A j ∧ s ≤ arrival ω j ∧ arrival ω j < t}
    (serviceReq ω) j

/-- Reflected backlog of the `A` jobs just before `t`. -/
noncomputable def backlogA {M : ℕ} (ω : Omega M) (A : Job M → Prop) (t : ℝ) : ℝ :=
  max 0 (sSup ((fun s => workA ω A s t - (t - s)) '' Set.Icc 0 t))

/-- Drop the class-`i` jobs of index `≥ J`. -/
def trunc {M : ℕ} (A : Job M → Prop) (i : Fin M) (J : ℕ) : Job M → Prop :=
  fun q => A q ∧ (q.1 = i → q.2 < J)

section Det
variable {M : ℕ} (ω : Omega M)

/-- Pointwise good path: nonnegative services, finitely many arrivals before each time. -/
def FinGood : Prop :=
  (∀ q : Job M, 0 ≤ serviceReq ω q) ∧ ∀ t : ℝ, {q : Job M | arrival ω q < t}.Finite

theorem workA_summable {ω : Omega M} (hG : FinGood ω) (A : Job M → Prop) (s t : ℝ) :
    Summable (Set.indicator {j : Job M | A j ∧ s ≤ arrival ω j ∧ arrival ω j < t}
      (serviceReq ω)) := by
  refine summable_of_ne_finset_zero (s := (hG.2 t).toFinset) (fun q hq => ?_)
  refine indicator_of_notMem (fun h => hq ?_) _
  exact (hG.2 t).mem_toFinset.2 h.2.2

theorem workA_nonneg {ω : Omega M} (hG : FinGood ω) (A : Job M → Prop) (s t : ℝ) :
    0 ≤ workA ω A s t :=
  tsum_nonneg (fun q => indicator_nonneg (fun q _ => hG.1 q) q)

theorem workA_mono {ω : Omega M} (hG : FinGood ω) {A A' : Job M → Prop} (hA : ∀ q, A q → A' q)
    {s s' t t' : ℝ} (hs : s' ≤ s) (ht : t ≤ t') : workA ω A s t ≤ workA ω A' s' t' := by
  refine Summable.tsum_le_tsum (fun q => ?_) (workA_summable hG A s t) (workA_summable hG A' s' t')
  refine indicator_le_indicator_of_subset (fun q hq => by
    obtain ⟨h1, h2, h3⟩ := hq
    exact ⟨hA q h1, hs.trans h2, h3.trans_le ht⟩) (fun q => hG.1 q) q

/-- Extra jobs that arrive at or after `t` do not change the work before `t`. -/
theorem workA_eq_of {A A' : Job M → Prop} (hA : ∀ q, A q → A' q)
    {s t : ℝ} (hx : ∀ q, A' q → ¬ A q → t ≤ arrival ω q) : workA ω A' s t = workA ω A s t := by
  unfold workA
  refine tsum_congr (fun q => ?_)
  by_cases hq : A q
  · have : A' q := hA q hq
    simp only [indicator, mem_setOf_eq, hq, this, true_and]
  · by_cases hq' : A' q
    · have h1 := hx q hq' hq
      rw [indicator_of_notMem (fun h => absurd h.2.2 (not_lt.2 h1)),
        indicator_of_notMem (fun h => hq h.1)]
    · rw [indicator_of_notMem (fun h => hq' h.1), indicator_of_notMem (fun h => hq h.1)]

theorem backlogA_mono {ω : Omega M} (hG : FinGood ω) {A A' : Job M → Prop} (hA : ∀ q, A q → A' q)
    (t : ℝ) : backlogA ω A t ≤ backlogA ω A' t := by
  unfold backlogA
  refine max_le_max le_rfl ?_
  rcases lt_or_ge t 0 with ht | ht
  · rw [Icc_eq_empty (not_le.2 ht)]
    simp only [image_empty]
    exact le_rfl
  have hbdd : BddAbove ((fun s => workA ω A' s t - (t - s)) '' Set.Icc 0 t) := by
    refine ⟨workA ω A' 0 t, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    have := workA_mono hG (fun q h => h) hs.1 (le_refl t) (A := A')
    dsimp only
    linarith [hs.2]
  refine csSup_le ((nonempty_Icc.2 ht).image _) ?_
  rintro _ ⟨s, hs, rfl⟩
  refine le_csSup_of_le hbdd ⟨s, hs, rfl⟩ ?_
  dsimp only
  linarith [workA_mono hG hA (le_refl s) (le_refl t)]

theorem backlogA_eq_of {A A' : Job M → Prop} (hA : ∀ q, A q → A' q) {t : ℝ}
    (hx : ∀ q, A' q → ¬ A q → t ≤ arrival ω q) : backlogA ω A' t = backlogA ω A t := by
  unfold backlogA
  congr 2
  refine image_congr (fun s _ => ?_)
  rw [workA_eq_of ω hA hx]

theorem backlogA_nonneg (A : Job M → Prop) (t : ℝ) : 0 ≤ backlogA ω A t := le_max_left _ _

/-- Deadline `J` of the W2 stopping structure: capped busy period of the truncated system. -/
noncomputable def Dl (Ag Ah : Job M → Prop) (i : Fin M) (T X c : ℝ) (J : ℕ) : ℝ :=
  T + bpc (backlogA ω (trunc Ag i J) T + X) c (fun u => workA ω (trunc Ah i J) T (T + u))

/-- The full capped busy-period end `T + τ^c`. -/
noncomputable def nuc (Ag Ah : Job M → Prop) (T X c : ℝ) : ℝ :=
  T + bpc (backlogA ω Ag T + X) c (fun u => workA ω Ah T (T + u))

theorem workT_mono {ω : Omega M} (hG : FinGood ω) (A : Job M → Prop) (T : ℝ) :
    Monotone (fun u => workA ω A T (T + u)) :=
  fun _ _ h => workA_mono hG (fun q h => h) le_rfl (by linarith)

theorem Dl_mono {ω : Omega M} (hG : FinGood ω) (Ag Ah : Job M → Prop) (i : Fin M) (T X c : ℝ)
    (hc : 0 ≤ c) : Monotone (Dl ω Ag Ah i T X c) := by
  intro J J' hJ
  unfold Dl
  have htr : ∀ A : Job M → Prop, ∀ q, trunc A i J q → trunc A i J' q :=
    fun A q h => ⟨h.1, fun hi => (h.2 hi).trans_le hJ⟩
  have := bpc_mono (x := backlogA ω (trunc Ag i J) T + X) (x' := backlogA ω (trunc Ag i J') T + X)
    hc (by linarith [backlogA_mono hG (htr Ag) T])
    (fun u => workA_mono hG (htr Ah) le_rfl le_rfl) (w := fun u => workA ω (trunc Ah i J) T (T + u))
    (w' := fun u => workA ω (trunc Ah i J') T (T + u))
  linarith

theorem Dl_ge {ω : Omega M} (Ag Ah : Job M → Prop) (i : Fin M) (T X c : ℝ) (hc : 0 ≤ c) (J : ℕ) :
    T ≤ Dl ω Ag Ah i T X c J := by
  unfold Dl; linarith [bpc_nonneg (x := backlogA ω (trunc Ag i J) T + X)
    (fun u => workA ω (trunc Ah i J) T (T + u)) hc]

/-- At the stopping index (first class-`i` arrival at or after its deadline) the truncated
deadline is the full capped busy-period end. -/
theorem Dl_stop {ω : Omega M} (hG : FinGood ω) (Ag Ah : Job M → Prop) (i : Fin M) (T X c : ℝ)
    (hc : 0 ≤ c) (L : ℕ) (harr : ∀ m, L ≤ m → arrival ω (i, L) ≤ arrival ω (i, m))
    (hL : Dl ω Ag Ah i T X c L ≤ arrival ω (i, L)) :
    Dl ω Ag Ah i T X c L = nuc ω Ag Ah T X c := by
  have hext : ∀ A : Job M → Prop, ∀ q, A q → ¬ trunc A i L q → Dl ω Ag Ah i T X c L ≤ arrival ω q := by
    intro A q hq hn
    have hqi : q.1 = i ∧ L ≤ q.2 := by
      by_contra hc'
      apply hn
      refine ⟨hq, fun hi => ?_⟩
      by_contra h2
      exact hc' ⟨hi, not_lt.1 h2⟩
    obtain ⟨q1, q2⟩ := q
    obtain ⟨rfl, h2⟩ := hqi
    exact hL.trans (harr q2 h2)
  have hT := Dl_ge (ω := ω) Ag Ah i T X c hc L
  have hb : backlogA ω Ag T = backlogA ω (trunc Ag i L) T :=
    backlogA_eq_of ω (fun q h => h.1) (fun q hq hn => hT.trans (hext Ag q hq hn))
  unfold nuc
  rw [hb]
  unfold Dl
  congr 1
  refine (bpc_local hc (workT_mono hG _ T) (fun u => workA_mono hG (fun q h => h.1) le_rfl le_rfl)
    ?_).symm
  refine workA_eq_of ω (fun q h => h.1) (fun q hq hn => ?_)
  have := hext Ah q hq hn
  unfold Dl at this
  exact this

end Det

section Upd
variable {M : ℕ} (ω : Omega M) (i : Fin M) (m : ℕ) (x : ℝ)

/-- Resample class-`i` interarrival `m`. -/
def upd : Omega M := (Function.update ω.1 (i, m) x, ω.2)

theorem arrival_upd (q : Job M) :
    arrival (upd ω i m x) q = arrival ω q +
      (if q.1 = i ∧ m ≤ q.2 then x - ω.1 (i, m) else 0) := by
  have hpt : ∀ k, Function.update ω.1 (i, m) x (q.1, k) =
      ω.1 (q.1, k) + (if q.1 = i ∧ k = m then x - ω.1 (i, m) else 0) := by
    intro k
    by_cases hk : q.1 = i ∧ k = m
    · obtain ⟨h1, h2⟩ := hk
      rw [if_pos ⟨h1, h2⟩, h1, h2, Function.update_self]
      ring
    · rw [if_neg hk, Function.update_of_ne (fun e => hk ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩)]
      ring
  unfold arrival upd
  dsimp only
  rw [Finset.sum_congr rfl (fun k _ => hpt k), Finset.sum_add_distrib]
  congr 1
  by_cases hq1 : q.1 = i
  · simp only [hq1, true_and, Finset.sum_ite_eq', Finset.mem_range]
    by_cases hm : m ≤ q.2
    · rw [if_pos (by omega), if_pos hm]
    · rw [if_neg (by omega), if_neg hm]
  · simp [hq1]

theorem arrival_upd_of {q : Job M} (hq : q.1 = i → q.2 < m) :
    arrival (upd ω i m x) q = arrival ω q := by
  rw [arrival_upd, if_neg (fun h => absurd (hq h.1) (by omega)), add_zero]

theorem serviceReq_upd : serviceReq (upd ω i m x) = serviceReq ω := rfl

theorem FinGood_upd {ω : Omega M} (hG : FinGood ω) : FinGood (upd ω i m x) := by
  refine ⟨fun q => by rw [serviceReq_upd]; exact hG.1 q, fun t => ?_⟩
  refine (hG.2 (t + |x - ω.1 (i, m)|)).subset (fun q hq => ?_)
  simp only [mem_setOf_eq] at hq ⊢
  rw [arrival_upd] at hq
  split_ifs at hq
  · linarith [neg_abs_le (x - ω.1 (i, m))]
  · linarith [abs_nonneg (x - ω.1 (i, m))]

theorem FinGood_upd_iff : FinGood (upd ω i m x) ↔ FinGood ω := by
  refine ⟨fun h => ?_, FinGood_upd i m x⟩
  have := FinGood_upd i m (ω.1 (i, m)) h
  have e : upd (upd ω i m x) i m (ω.1 (i, m)) = ω := by
    unfold upd
    simp only [Function.update_idem, Function.update_eq_self]
  rwa [e] at this

variable {i m}

theorem workA_trunc_upd (A : Job M → Prop) {J : ℕ} (hJ : J ≤ m) (s t : ℝ) :
    workA (upd ω i m x) (trunc A i J) s t = workA ω (trunc A i J) s t := by
  unfold workA
  refine tsum_congr (fun q => ?_)
  by_cases hq : trunc A i J q
  · have ha := arrival_upd_of ω i m x (q := q) (fun h => (hq.2 h).trans_le hJ)
    have hmem : (q ∈ {j : Job M | trunc A i J j ∧ s ≤ arrival (upd ω i m x) j ∧
        arrival (upd ω i m x) j < t}) ↔ (q ∈ {j : Job M | trunc A i J j ∧ s ≤ arrival ω j ∧
        arrival ω j < t}) := by
      show (_ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
      rw [ha]
    by_cases h : q ∈ {j : Job M | trunc A i J j ∧ s ≤ arrival ω j ∧ arrival ω j < t}
    · rw [indicator_of_mem (hmem.2 h), indicator_of_mem h]
      rfl
    · rw [indicator_of_notMem (fun h' => h (hmem.1 h')), indicator_of_notMem h]
  · rw [indicator_of_notMem (fun h => hq h.1), indicator_of_notMem (fun h => hq h.1)]

theorem backlogA_trunc_upd (A : Job M → Prop) {J : ℕ} (hJ : J ≤ m) (t : ℝ) :
    backlogA (upd ω i m x) (trunc A i J) t = backlogA ω (trunc A i J) t := by
  unfold backlogA
  simp only [workA_trunc_upd ω x A hJ]

/-- W2 invariance: the deadline `J` ignores class-`i` interarrivals of index `≥ J`. -/
theorem Dl_upd (Ag Ah : Job M → Prop) (T X c : ℝ) {J : ℕ} (hJ : J ≤ m) :
    Dl (upd ω i m x) Ag Ah i T X c J = Dl ω Ag Ah i T X c J := by
  unfold Dl
  simp only [backlogA_trunc_upd ω x Ag hJ, workA_trunc_upd ω x Ah hJ]

end Upd
end CM4T

/-! relay 12: measurability (C2 step (a)). Measurable versions `workAm`, `backlogM`, and the
`if FinGood then .. else 0` wrappers of `bpc` and `Dl`, via countable characterisations:
backlog sup attained at arrival points; capped busy period `< c` is a fixed point `x + w u = u`,
hence `x + (finite sum of services)`. -/
namespace CM4M
open Set CoffmanMitrani CM4B CM4T MeasureTheory

variable {M : ℕ}

theorem measurable_arrival (j : Job M) : Measurable (fun ω : Omega M => arrival ω j) := by
  unfold arrival
  exact Finset.measurable_sum _ (fun m _ => (measurable_pi_apply _).comp measurable_fst)

theorem measurable_serviceReq (j : Job M) : Measurable (fun ω : Omega M => serviceReq ω j) := by
  unfold serviceReq
  exact (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)

theorem measurableSet_FinGood : MeasurableSet {ω : Omega M | FinGood ω} := by
  have : {ω : Omega M | FinGood ω} = (⋂ q : Job M, {ω | 0 ≤ serviceReq ω q}) ∩
      ⋂ n : ℕ, ⋃ F : Finset (Job M), ⋂ q : Job M, {ω | q ∈ F ∨ (n : ℝ) ≤ arrival ω q} := by
    ext ω
    simp only [mem_setOf_eq, mem_inter_iff, mem_iInter, mem_iUnion, FinGood]
    refine and_congr Iff.rfl ⟨fun h n => ?_, fun h t => ?_⟩
    · refine ⟨(h n).toFinset, fun q => ?_⟩
      by_cases hq : arrival ω q < n
      · exact Or.inl ((h n).mem_toFinset.2 hq)
      · exact Or.inr (not_lt.1 hq)
    · obtain ⟨n, hn⟩ := exists_nat_ge t
      obtain ⟨F, hF⟩ := h n
      refine F.finite_toSet.subset (fun q hq => ?_)
      rcases hF q with h1 | h1
      · exact h1
      · exact absurd (lt_of_lt_of_le (show arrival ω q < t from hq) hn) (not_lt.2 h1)
  rw [this]
  refine (MeasurableSet.iInter fun q => measurableSet_le measurable_const (measurable_serviceReq q)).inter
    (MeasurableSet.iInter fun n => MeasurableSet.iUnion fun F => MeasurableSet.iInter fun q => ?_)
  by_cases hq : q ∈ F
  · simp [hq]
  · simpa [hq] using measurableSet_le measurable_const (measurable_arrival q)

/-- Work as an `ℝ≥0∞` sum (measurable; equals `workA` when services are nonnegative). -/
noncomputable def workAm (ω : Omega M) (A : Job M → Prop) (s t : ℝ) : ℝ :=
  (∑' j : Job M, ENNReal.ofReal (Set.indicator {j : Job M | A j ∧ s ≤ arrival ω j ∧ arrival ω j < t}
    (serviceReq ω) j)).toReal

theorem workAm_eq {ω : Omega M} (h : ∀ q, 0 ≤ serviceReq ω q) (A : Job M → Prop) (s t : ℝ) :
    workAm ω A s t = workA ω A s t := by
  unfold workAm workA
  rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  exact tsum_congr (fun j => ENNReal.toReal_ofReal (indicator_nonneg (fun q _ => h q) j))

theorem measurable_workAm (A : Job M → Prop) {s t : Omega M → ℝ} (hs : Measurable s)
    (ht : Measurable t) : Measurable (fun ω => workAm ω A (s ω) (t ω)) := by
  refine (Measurable.ennreal_tsum (fun j => ?_)).ennreal_toReal
  refine ENNReal.measurable_ofReal.comp ?_
  by_cases hA : A j
  · have hm : MeasurableSet {ω : Omega M | s ω ≤ arrival ω j ∧ arrival ω j < t ω} :=
      (measurableSet_le hs (measurable_arrival j)).inter (measurableSet_lt (measurable_arrival j) ht)
    have : (fun ω => Set.indicator {j' : Job M | A j' ∧ s ω ≤ arrival ω j' ∧ arrival ω j' < t ω}
        (serviceReq ω) j) = Set.indicator {ω | s ω ≤ arrival ω j ∧ arrival ω j < t ω}
        (fun ω => serviceReq ω j) := by
      funext ω; simp only [Set.indicator, mem_setOf_eq, hA, true_and]
    rw [this]; exact (measurable_serviceReq j).indicator hm
  · have : (fun ω => Set.indicator {j' : Job M | A j' ∧ s ω ≤ arrival ω j' ∧ arrival ω j' < t ω}
        (serviceReq ω) j) = fun _ => 0 := by
      funext ω; exact indicator_of_notMem (fun h => hA h.1) _
    rw [this]; exact measurable_const

open scoped Classical in
/-- Candidate value of the backlog sup at the arrival point of job `q`. -/
noncomputable def bq (ω : Omega M) (A : Job M → Prop) (t : ℝ) (q : Job M) : ℝ :=
  if A q ∧ 0 ≤ arrival ω q ∧ arrival ω q < t then
    max 0 (workA ω A (arrival ω q) t - (t - arrival ω q)) else 0

open scoped Classical in
noncomputable def bqm (ω : Omega M) (A : Job M → Prop) (t : ℝ) (q : Job M) : ℝ :=
  if A q ∧ 0 ≤ arrival ω q ∧ arrival ω q < t then
    max 0 (workAm ω A (arrival ω q) t - (t - arrival ω q)) else 0

theorem bq_nonneg (ω : Omega M) (A : Job M → Prop) (t : ℝ) (q : Job M) : 0 ≤ bq ω A t q := by
  unfold bq; split_ifs <;> simp

theorem bq_le {ω : Omega M} (hG : FinGood ω) (A : Job M → Prop) (t : ℝ) (q : Job M) :
    bq ω A t q ≤ workA ω A 0 t := by
  unfold bq; split_ifs with h
  · refine max_le (workA_nonneg hG A 0 t) ?_
    have := workA_mono hG (fun q h => h) h.2.1 (le_refl t) (A := A)
    linarith [h.2.2]
  · exact workA_nonneg hG A 0 t

/-- The backlog sup is attained at arrival points (or is `0`). -/
theorem backlogA_eq_iSup {ω : Omega M} (hG : FinGood ω) (A : Job M → Prop) (t : ℝ) :
    backlogA ω A t = ⨆ q, bq ω A t q := by
  have hbdd : BddAbove (Set.range (bq ω A t)) :=
    ⟨workA ω A 0 t, by rintro _ ⟨q, rfl⟩; exact bq_le hG A t q⟩
  have h0 : 0 ≤ ⨆ q, bq ω A t q := Real.iSup_nonneg (fun q => bq_nonneg ω A t q)
  unfold backlogA
  have hfb : BddAbove ((fun s => workA ω A s t - (t - s)) '' Icc 0 t) := ⟨workA ω A 0 t, by
    rintro _ ⟨s, hs, rfl⟩
    have := workA_mono hG (fun q h => h) hs.1 (le_refl t) (A := A)
    dsimp only; linarith [hs.2]⟩
  apply le_antisymm
  · refine max_le h0 ?_
    rcases lt_or_ge t 0 with ht | ht
    · rw [Icc_eq_empty (not_le.2 ht), image_empty, Real.sSup_empty]
      exact h0
    refine csSup_le ((nonempty_Icc.2 ht).image _) ?_
    rintro _ ⟨s, hs, rfl⟩
    dsimp only
    have hSf : {q : Job M | A q ∧ s ≤ arrival ω q ∧ arrival ω q < t}.Finite :=
      (hG.2 t).subset (fun q hq => hq.2.2)
    rcases Set.eq_empty_or_nonempty {q : Job M | A q ∧ s ≤ arrival ω q ∧ arrival ω q < t}
      with he | hne
    · have hw0 : workA ω A s t = 0 := by
        unfold workA
        refine (tsum_congr (fun q => ?_)).trans tsum_zero
        refine indicator_of_notMem ?_ _
        rw [he]; exact notMem_empty q
      rw [hw0]; linarith [hs.2]
    · obtain ⟨q, hq, hmin⟩ := Set.exists_min_image _ (fun q => arrival ω q) hSf hne
      have hse : {j : Job M | A j ∧ s ≤ arrival ω j ∧ arrival ω j < t} =
          {j : Job M | A j ∧ arrival ω q ≤ arrival ω j ∧ arrival ω j < t} := by
        ext j'
        simp only [mem_setOf_eq]
        constructor
        · rintro ⟨h1, h2, h3⟩; exact ⟨h1, hmin j' ⟨h1, h2, h3⟩, h3⟩
        · rintro ⟨h1, h2, h3⟩; exact ⟨h1, hq.2.1.trans h2, h3⟩
      have hw : workA ω A s t = workA ω A (arrival ω q) t := by
        unfold workA; rw [hse]
      have hcond : A q ∧ 0 ≤ arrival ω q ∧ arrival ω q < t := ⟨hq.1, hs.1.trans hq.2.1, hq.2.2⟩
      refine le_trans ?_ (le_ciSup hbdd q)
      rw [bq, if_pos hcond, hw]
      exact le_max_of_le_right (by linarith [hq.2.1])
  · refine Real.iSup_le (fun q => ?_) (le_max_left _ _)
    unfold bq
    split_ifs with h
    · exact max_le_max le_rfl (le_csSup hfb ⟨arrival ω q, ⟨h.2.1, h.2.2.le⟩, rfl⟩)
    · exact le_max_left _ _

theorem measurable_bqm (A : Job M → Prop) {t : Omega M → ℝ} (ht : Measurable t) (q : Job M) :
    Measurable (fun ω => bqm ω A (t ω) q) := by
  have hm : MeasurableSet {ω : Omega M | A q ∧ 0 ≤ arrival ω q ∧ arrival ω q < t ω} := by
    by_cases hA : A q
    · simp only [hA, true_and]
      exact (measurableSet_le measurable_const (measurable_arrival q)).inter
        (measurableSet_lt (measurable_arrival q) ht)
    · simp only [hA, false_and, setOf_false, MeasurableSet.empty]
  unfold bqm
  exact Measurable.ite hm (measurable_const.max ((measurable_workAm A (measurable_arrival q) ht).sub
    (ht.sub (measurable_arrival q)))) measurable_const

/-- Measurable backlog. -/
noncomputable def backlogM (ω : Omega M) (A : Job M → Prop) (t : ℝ) : ℝ := ⨆ q, bqm ω A t q

theorem measurable_backlogM (A : Job M → Prop) {t : Omega M → ℝ} (ht : Measurable t) :
    Measurable (fun ω => backlogM ω A (t ω)) :=
  Measurable.iSup (fun q => measurable_bqm A ht q)

theorem backlogM_eq {ω : Omega M} (hG : FinGood ω) (A : Job M → Prop) (t : ℝ) :
    backlogM ω A t = backlogA ω A t := by
  rw [backlogA_eq_iSup hG]
  unfold backlogM bqm bq
  simp only [workAm_eq hG.1]

/-- On a good path the work over an interval is a finite sum of service requirements. -/
theorem workA_eq_sum {ω : Omega M} (hG : FinGood ω) (A : Job M → Prop) (s t : ℝ) :
    ∃ F : Finset (Job M), workA ω A s t = ∑ q ∈ F, serviceReq ω q := by
  classical
  refine ⟨(hG.2 t).toFinset.filter (fun q => A q ∧ s ≤ arrival ω q ∧ arrival ω q < t), ?_⟩
  unfold workA
  rw [tsum_eq_sum (s := (hG.2 t).toFinset) (fun q hq => indicator_of_notMem
    (fun h => hq ((hG.2 t).mem_toFinset.2 h.2.2)) _), Finset.sum_filter]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  by_cases h : A q ∧ s ≤ arrival ω q ∧ arrival ω q < t
  · rw [if_pos h, indicator_of_mem (show q ∈ {j : Job M | A j ∧ s ≤ arrival ω j ∧ arrival ω j < t} from h)]
  · rw [if_neg h, indicator_of_notMem (show q ∉ {j : Job M | A j ∧ s ≤ arrival ω j ∧ arrival ω j < t} from h)]

/-- Below the cap, the capped busy period is a fixed point `x + w u = u`. -/
theorem bpc_fix {x c : ℝ} {w : ℝ → ℝ} (hc : 0 ≤ c) (hw : Monotone w) (hx0 : 0 ≤ x)
    (hw0 : ∀ u, 0 ≤ w u) (hlt : bpc x c w < c) : x + w (bpc x c w) = bpc x c w := by
  have hm := bpc_mem (x := x) hc hw
  rcases hm.2 with h | h
  · refine le_antisymm h ?_
    by_contra hne
    push Not at hne
    have hu : x + w (bpc x c w) ∈ bpS x c w :=
      ⟨by linarith [hw0 (bpc x c w)], Or.inl (by linarith [hw hne.le])⟩
    linarith [bpc_le_of_mem hu]
  · linarith

/-- Countable characterisation of `bpc ≤ v` on a good path. -/
theorem bpc_le_iff_fin {ω : Omega M} (hG : FinGood ω) (A : Job M → Prop) (T x c v : ℝ)
    (hc : 0 ≤ c) (hx : 0 ≤ x) :
    bpc x c (fun u => workA ω A T (T + u)) ≤ v ↔ c ≤ v ∨ ∃ F : Finset (Job M),
      0 ≤ x + ∑ q ∈ F, serviceReq ω q ∧ x + ∑ q ∈ F, serviceReq ω q ≤ v ∧
      x + workA ω A T (T + (x + ∑ q ∈ F, serviceReq ω q)) ≤ x + ∑ q ∈ F, serviceReq ω q := by
  have hw := workT_mono hG A T
  have hw0 : ∀ u, 0 ≤ workA ω A T (T + u) := fun u => workA_nonneg hG A T (T + u)
  constructor
  · intro hle
    by_cases hcv : c ≤ v
    · exact Or.inl hcv
    right
    push Not at hcv
    set b := bpc x c (fun u => workA ω A T (T + u)) with hb
    have hlt : b < c := lt_of_le_of_lt hle hcv
    have hfix : x + workA ω A T (T + b) = b := bpc_fix hc hw hx hw0 hlt
    obtain ⟨F, hF⟩ := workA_eq_sum hG A T (T + b)
    refine ⟨F, ?_⟩
    rw [← hF, hfix]
    exact ⟨bpc_nonneg _ hc, hle, hfix.le⟩
  · rintro (h | ⟨F, h1, h2, h3⟩)
    · exact (bpc_le_c _ hc).trans h
    · exact (bpc_le_of_mem ⟨h1, Or.inl h3⟩).trans h2

open scoped Classical in
theorem measurable_bpcG (A : Job M → Prop) {x T : Omega M → ℝ} (hx : Measurable x)
    (hT : Measurable T) (hx0 : ∀ ω, FinGood ω → 0 ≤ x ω) {c : ℝ} (hc : 0 ≤ c) :
    Measurable (fun ω => if FinGood ω then bpc (x ω) c (fun u => workA ω A (T ω) (T ω + u))
      else 0) := by
  classical
  refine measurable_of_Iic (fun v => ?_)
  have hym : ∀ F : Finset (Job M), Measurable (fun ω => x ω + ∑ q ∈ F, serviceReq ω q) :=
    fun F => hx.add (Finset.measurable_sum F (fun q _ => measurable_serviceReq q))
  have hset : (fun ω => if FinGood ω then bpc (x ω) c (fun u => workA ω A (T ω) (T ω + u))
      else 0) ⁻¹' Iic v =
      ({ω | FinGood ω}ᶜ ∩ {_ω | 0 ≤ v}) ∪ ({ω | FinGood ω} ∩ ({_ω | c ≤ v} ∪
        ⋃ F : Finset (Job M), ({ω | 0 ≤ x ω + ∑ q ∈ F, serviceReq ω q} ∩
          {ω | x ω + ∑ q ∈ F, serviceReq ω q ≤ v} ∩
          {ω | x ω + workAm ω A (T ω) (T ω + (x ω + ∑ q ∈ F, serviceReq ω q)) ≤
            x ω + ∑ q ∈ F, serviceReq ω q}))) := by
    ext ω
    by_cases hω : FinGood ω
    · have key := bpc_le_iff_fin hω A (T ω) (x ω) c v hc (hx0 ω hω)
      simp only [mem_preimage, mem_Iic, if_pos hω, mem_union, mem_inter_iff, mem_compl_iff,
        mem_setOf_eq, hω, not_true_eq_false, false_and, false_or, true_and, mem_iUnion,
        workAm_eq hω.1, and_assoc]
      exact key
    · simp only [mem_preimage, mem_Iic, if_neg hω, mem_union, mem_inter_iff, mem_compl_iff,
        mem_setOf_eq, hω, not_false_eq_true, true_and, false_and, or_false, ↓reduceIte]
  rw [hset]
  refine (measurableSet_FinGood.compl.inter (MeasurableSet.const _)).union
    (measurableSet_FinGood.inter ((MeasurableSet.const _).union (MeasurableSet.iUnion fun F => ?_)))
  exact ((measurableSet_le measurable_const (hym F)).inter
    (measurableSet_le (hym F) measurable_const)).inter
    (measurableSet_le ((hx.add (measurable_workAm A hT (hT.add (hym F)))))
      (hym F))

open scoped Classical in
/-- The W2 deadlines, wrapped to `0` off the good set, are measurable. -/
theorem measurable_DlG (Ag Ah : Job M → Prop) (i : Fin M) {T X : Omega M → ℝ}
    (hT : Measurable T) (hX : Measurable X) (hX0 : ∀ ω, FinGood ω → 0 ≤ X ω) {c : ℝ}
    (hc : 0 ≤ c) (J : ℕ) :
    Measurable (fun ω => if FinGood ω then Dl ω Ag Ah i (T ω) (X ω) c J else 0) := by
  classical
  have hx0 : ∀ ω, FinGood ω → 0 ≤ backlogM ω (trunc Ag i J) (T ω) + X ω := fun ω hω => by
    rw [backlogM_eq hω]; exact add_nonneg (backlogA_nonneg ω _ _) (hX0 ω hω)
  have hb := measurable_bpcG (trunc Ah i J) ((measurable_backlogM (trunc Ag i J) hT).add hX) hT
    hx0 hc
  have heq : (fun ω => if FinGood ω then Dl ω Ag Ah i (T ω) (X ω) c J else 0) =
      fun ω => (if FinGood ω then T ω else 0) + (if FinGood ω then
        bpc (backlogM ω (trunc Ag i J) (T ω) + X ω) c
          (fun u => workA ω (trunc Ah i J) (T ω) (T ω + u)) else 0) := by
    funext ω
    by_cases hω : FinGood ω
    · simp only [if_pos hω, Dl, backlogM_eq hω]
    · simp only [if_neg hω, add_zero]
  rw [heq]
  exact (Measurable.ite measurableSet_FinGood hT measurable_const).add hb

end CM4M

/-! relay 12: W2 at the capped busy-period end (`wald_bp`). -/
namespace CM4V
open MeasureTheory Set CoffmanMitrani CM4B CM4T CM4M CM4W

variable {M : ℕ}

open scoped Classical in
/-- Measurable-wrapped W2 deadline. -/
noncomputable def DlG (Ag Ah : Job M → Prop) (i : Fin M) (T X : Omega M → ℝ) (c : ℝ) (J : ℕ)
    (ω : Omega M) : ℝ :=
  if FinGood ω then Dl ω Ag Ah i (T ω) (X ω) c J else 0

/-- Residual deadline after the first `m` class-`i` interarrivals. -/
noncomputable def gW (Ag Ah : Job M → Prop) (i : Fin M) (T X : Omega M → ℝ) (c : ℝ) (m : ℕ)
    (ω : Omega M) : ℝ :=
  max 0 (DlG Ag Ah i T X c m ω - ∑ k ∈ Finset.range m, ω.1 (i, k))

theorem stop_exists {ω : Omega M} (hG : FinGood ω) (i : Fin M) (hpos : ∀ k, 0 ≤ ω.1 (i, k))
    (Ag Ah : Job M → Prop) (T X c : ℝ) (hc : 0 ≤ c) :
    ∃ L, (∀ j < L, ∑ k ∈ Finset.range (j + 1), ω.1 (i, k) < Dl ω Ag Ah i T X c j) ∧
      Dl ω Ag Ah i T X c L ≤ ∑ k ∈ Finset.range (L + 1), ω.1 (i, k) ∧
      Dl ω Ag Ah i T X c L = nuc ω Ag Ah T X c := by
  classical
  have hfin : {j : ℕ | arrival ω (i, j) < T + c}.Finite :=
    (hG.2 (T + c)).preimage (fun a _ b _ h => by simpa using h)
  obtain ⟨N, hN⟩ := hfin.bddAbove
  have hex : ∃ j, Dl ω Ag Ah i T X c j ≤ ∑ k ∈ Finset.range (j + 1), ω.1 (i, k) := by
    refine ⟨N + 1, ?_⟩
    have h1 : ¬ arrival ω (i, N + 1) < T + c := fun h => by
      have := hN (show N + 1 ∈ {j : ℕ | arrival ω (i, j) < T + c} from h)
      omega
    have h2 : Dl ω Ag Ah i T X c (N + 1) ≤ T + c := by
      unfold Dl; linarith [bpc_le_c (x := backlogA ω (trunc Ag i (N + 1)) T + X)
        (fun u => workA ω (trunc Ah i (N + 1)) T (T + u)) hc]
    have h3 : arrival ω (i, N + 1) = ∑ k ∈ Finset.range (N + 1 + 1), ω.1 (i, k) := rfl
    linarith [not_lt.1 h1]
  refine ⟨Nat.find hex, fun j hj => not_le.1 (Nat.find_min hex hj), Nat.find_spec hex, ?_⟩
  refine Dl_stop hG Ag Ah i T X c hc _ (fun m hm => ?_) (Nat.find_spec hex)
  show ∑ k ∈ Finset.range (Nat.find hex + 1), ω.1 (i, k) ≤ ∑ k ∈ Finset.range (m + 1), ω.1 (i, k)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun k _ _ => hpos k)

/-- W2 at the capped busy-period end: `λ_i E[T + τ^c] = Σ_m P(a_{i,m} < T + τ^c)`. -/
theorem wald_bp (D : Data) (i : Fin D.M) (Ag Ah : Job D.M → Prop) (T X : Omega D.M → ℝ)
    (hT : Measurable T) (hX : Measurable X) (hX0 : ∀ ω, FinGood ω → 0 ≤ X ω)
    (hTinv : ∀ m ω x, T (upd ω i m x) = T ω) (hXinv : ∀ m ω x, X (upd ω i m x) = X ω)
    {c : ℝ} (hc : 0 ≤ c)
    (hgood : ∀ᵐ ω ∂D.P, FinGood ω ∧ (∀ k, 0 ≤ ω.1 (i, k)) ∧ 0 ≤ T ω) :
    ENNReal.ofReal (D.lam i) * ∫⁻ ω, ENNReal.ofReal (nuc ω Ag Ah (T ω) (X ω) c) ∂D.P =
      ∑' m, D.P {ω | ∑ k ∈ Finset.range (m + 1), ω.1 (i, k) < nuc ω Ag Ah (T ω) (X ω) c} := by
  classical
  have hgω : ∀ ω, FinGood ω → ∀ m, gW Ag Ah i T X c m ω =
      max 0 (Dl ω Ag Ah i (T ω) (X ω) c m - ∑ k ∈ Finset.range m, ω.1 (i, k)) :=
    fun ω hG m => by simp only [gW, DlG, if_pos hG]
  refine wald_count D i (gW Ag Ah i T X c) (fun ω => nuc ω Ag Ah (T ω) (X ω) c) (fun m => ?_)
    (fun m ω => le_max_left _ _) (fun j m ω x hjm => ?_) ?_ (fun m => ?_)
  · exact measurable_const.max ((measurable_DlG Ag Ah i hT hX hX0 hc m).sub
      (Finset.measurable_sum _ (fun k _ => (measurable_pi_apply _).comp measurable_fst)))
  · have h1 : DlG Ag Ah i T X c j (upd ω i m x) = DlG Ag Ah i T X c j ω := by
      simp only [DlG, FinGood_upd_iff, hTinv, hXinv, Dl_upd (i := i) ω x Ag Ah (T ω) (X ω) c hjm]
    have h2 : ∑ k ∈ Finset.range j, (upd ω i m x).1 (i, k) = ∑ k ∈ Finset.range j, ω.1 (i, k) :=
      Finset.sum_congr rfl (fun k hk => by
        have hk' : k < m := lt_of_lt_of_le (Finset.mem_range.1 hk) hjm
        simp only [upd]
        exact Function.update_of_ne (by simp [hk'.ne]) _ _)
    show max 0 (DlG Ag Ah i T X c j (upd ω i m x) -
      ∑ k ∈ Finset.range j, (upd ω i m x).1 (i, k)) = _
    rw [h1, h2]; rfl
  · filter_upwards [hgood] with ω ⟨hG, hpos, hT0⟩
    obtain ⟨L, hL, hLs, hnuc⟩ := stop_exists hG i hpos Ag Ah (T ω) (X ω) c hc
    have hs := stop_sum (fun k => ω.1 (i, k)) (Dl ω Ag Ah i (T ω) (X ω) c) hpos
      (Dl_mono hG Ag Ah i (T ω) (X ω) c hc)
      (hT0.trans (Dl_ge (ω := ω) Ag Ah i (T ω) (X ω) c hc 0)) L hL hLs
    show _ = ENNReal.ofReal (nuc ω Ag Ah (T ω) (X ω) c)
    rw [← hnuc, ← hs]
    refine tsum_congr (fun m => ?_)
    simp only [Set.indicator_apply, Aset, mem_setOf_eq, hgω ω hG]
  · filter_upwards [hgood] with ω ⟨hG, hpos, hT0⟩
    obtain ⟨L, hL, hLs, hnuc⟩ := stop_exists hG i hpos Ag Ah (T ω) (X ω) c hc
    have hcn := stop_cnt (fun k => ω.1 (i, k)) (Dl ω Ag Ah i (T ω) (X ω) c) hpos
      (Dl_mono hG Ag Ah i (T ω) (X ω) c hc) L hL hLs m
    show ω ∈ Aset D i (gW Ag Ah i T X c) (m + 1) ↔ _ < nuc ω Ag Ah (T ω) (X ω) c
    rw [← hnuc, ← hcn]
    simp only [Aset, mem_setOf_eq, hgω ω hG]

end CM4V

/-! relay 12: W3 invariance device. Zeroing the service of a job `j` that arrives at or after `T`
does not change the event `a_j < nuc` (the busy period before `a_j` never sees `X_j`), so
`B = {T ≤ a_j < nuc (zs ω j)}` is exactly invariant under service resampling (for `service_core`). -/
namespace CM4Z
open Set CoffmanMitrani CM4B CM4T

section
variable {M : ℕ} (ω : Omega M)

/-- Zero the service requirement of job `j`. -/
def zs (j : Job M) : Omega M := (ω.1, Function.update ω.2.1 j 0, ω.2.2)

theorem arrival_zs (j : Job M) : arrival (zs ω j) = arrival ω := rfl

theorem serviceReq_zs_ne {j q : Job M} (h : q ≠ j) : serviceReq (zs ω j) q = serviceReq ω q :=
  Function.update_of_ne h _ _

theorem FinGood_zs {ω : Omega M} (hG : FinGood ω) (j : Job M) : FinGood (zs ω j) := by
  refine ⟨fun q => ?_, fun t => hG.2 t⟩
  by_cases h : q = j
  · subst h
    show 0 ≤ Function.update ω.2.1 q 0 q
    simp
  · rw [serviceReq_zs_ne ω h]; exact hG.1 q

theorem workA_zs (j : Job M) (A : Job M → Prop) {s t : ℝ} (ht : t ≤ arrival ω j) :
    workA (zs ω j) A s t = workA ω A s t := by
  unfold workA
  refine tsum_congr (fun q => ?_)
  by_cases hq : q = j
  · subst hq
    rw [indicator_of_notMem (fun h => absurd h.2.2 (not_lt.2 ht)),
      indicator_of_notMem (fun h => absurd h.2.2 (not_lt.2 ht))]
  · simp only [arrival_zs]
    by_cases hm : q ∈ {j' : Job M | A j' ∧ s ≤ arrival ω j' ∧ arrival ω j' < t}
    · rw [indicator_of_mem hm, indicator_of_mem hm, serviceReq_zs_ne ω hq]
    · rw [indicator_of_notMem hm, indicator_of_notMem hm]

theorem backlogA_zs (j : Job M) (A : Job M → Prop) {t : ℝ} (ht : t ≤ arrival ω j) :
    backlogA (zs ω j) A t = backlogA ω A t := by
  unfold backlogA
  congr 2
  refine image_congr (fun s _ => ?_)
  rw [workA_zs ω j A ht]

theorem nuc_lt_iff_zs {ω : Omega M} (hG : FinGood ω) (j : Job M) (Ag Ah : Job M → Prop)
    (T X c : ℝ) (hc : 0 ≤ c) (hTj : T ≤ arrival ω j) :
    arrival ω j < nuc (zs ω j) Ag Ah T X c ↔ arrival ω j < nuc ω Ag Ah T X c := by
  have hG' := FinGood_zs hG j
  unfold nuc
  rw [backlogA_zs ω j Ag hTj]
  have key : ∀ ω' : Omega M, FinGood ω' →
      (bpc (backlogA ω Ag T + X) c (fun u => workA ω' Ah T (T + u)) ≤ arrival ω j - T ↔
        ∃ u ∈ bpS (backlogA ω Ag T + X) c (fun u => workA ω' Ah T (T + u)),
          u ≤ arrival ω j - T) :=
    fun ω' h => bpc_le_iff hc (workT_mono h Ah T)
  have hS : ∀ u, u ≤ arrival ω j - T →
      (u ∈ bpS (backlogA ω Ag T + X) c (fun u => workA (zs ω j) Ah T (T + u)) ↔
        u ∈ bpS (backlogA ω Ag T + X) c (fun u => workA ω Ah T (T + u))) := by
    intro u hu
    simp only [bpS, mem_setOf_eq, workA_zs ω j Ah (show T + u ≤ arrival ω j by linarith)]
  have e1 := key _ hG'
  have e2 := key _ hG
  constructor
  · intro h
    by_contra hn
    push Not at hn
    obtain ⟨u, hu, huv⟩ := e2.1 (by linarith)
    have := e1.2 ⟨u, (hS u huv).2 hu, huv⟩
    linarith
  · intro h
    by_contra hn
    push Not at hn
    obtain ⟨u, hu, huv⟩ := e1.1 (by linarith)
    have := e2.2 ⟨u, (hS u huv).1 hu, huv⟩
    linarith

end
end CM4Z

/-! ## CM4X (relay 13): W3, the service identity at the busy-period end. -/
namespace CM4X
open MeasureTheory Set CoffmanMitrani CM4B CM4T CM4M CM4W CM4V CM4Z

variable {M : ℕ}

open scoped Classical in
/-- Measurable-wrapped busy-period end. -/
noncomputable def nucG (Ag Ah : Job M → Prop) (T X : Omega M → ℝ) (c : ℝ) (ω : Omega M) : ℝ :=
  if FinGood ω then nuc ω Ag Ah (T ω) (X ω) c else 0

theorem measurable_nucG (Ag Ah : Job M → Prop) {T X : Omega M → ℝ}
    (hT : Measurable T) (hX : Measurable X) (hX0 : ∀ ω, FinGood ω → 0 ≤ X ω) {c : ℝ}
    (hc : 0 ≤ c) : Measurable (nucG Ag Ah T X c) := by
  classical
  have hx0 : ∀ ω, FinGood ω → 0 ≤ backlogM ω Ag (T ω) + X ω := fun ω hω => by
    rw [backlogM_eq hω]; exact add_nonneg (backlogA_nonneg ω _ _) (hX0 ω hω)
  have hb := measurable_bpcG Ah ((measurable_backlogM Ag hT).add hX) hT hx0 hc
  have heq : nucG Ag Ah T X c = fun ω => (if FinGood ω then T ω else 0) + (if FinGood ω then
        bpc (backlogM ω Ag (T ω) + X ω) c (fun u => workA ω Ah (T ω) (T ω + u)) else 0) := by
    funext ω
    by_cases hω : FinGood ω
    · simp only [nucG, if_pos hω, nuc, backlogM_eq hω]
    · simp only [nucG, if_neg hω, add_zero]
  rw [heq]
  exact (Measurable.ite measurableSet_FinGood hT measurable_const).add hb

theorem measurable_zs (j : Job M) : Measurable (fun ω : Omega M => zs ω j) := by
  have h2 : Measurable (fun ω : Omega M => Function.update ω.2.1 j 0) := by
    refine measurable_pi_lambda _ (fun q => ?_)
    by_cases h : q = j
    · subst h; simp only [Function.update_self]; exact measurable_const
    · simp only [Function.update_of_ne h]
      exact (measurable_pi_apply q).comp (measurable_fst.comp measurable_snd)
  exact measurable_fst.prodMk (h2.prodMk (measurable_snd.comp measurable_snd))

/-- Job `j` arrives inside the busy period `[T, nuc)`. -/
def Eset (T X : Omega M → ℝ) (Ag Ah : Job M → Prop) (c : ℝ) (j : Job M) : Set (Omega M) :=
  {ω | T ω ≤ arrival ω j ∧ arrival ω j < nuc ω Ag Ah (T ω) (X ω) c}

/-- W3 for one job: `μ_i E[X_j; T ≤ a_j < nuc] = P(T ≤ a_j < nuc)`. -/
theorem service_bp (D : Data) (j : Job D.M) (Ag Ah : Job D.M → Prop) (T X : Omega D.M → ℝ)
    (hT : Measurable T) (hX : Measurable X) (hX0 : ∀ ω, FinGood ω → 0 ≤ X ω) {c : ℝ}
    (hc : 0 ≤ c) (hTzs : ∀ ω, T (zs ω j) = T ω) (hXzs : ∀ ω, X (zs ω j) = X ω)
    (hgood : ∀ᵐ ω ∂D.P, FinGood ω) :
    ENNReal.ofReal (D.mu j.1) * ∫⁻ ω, (Eset T X Ag Ah c j).indicator
        (fun ω => ENNReal.ofReal (ω.2.1 j)) ω ∂D.P = D.P (Eset T X Ag Ah c j) ∧
      AEMeasurable ((Eset T X Ag Ah c j).indicator (fun ω => ENNReal.ofReal (ω.2.1 j))) D.P := by
  classical
  let G : Set (Omega D.M) :=
    {ω | FinGood ω} ∩ ({ω | T ω ≤ arrival ω j} ∩ {ω | arrival ω j < nucG Ag Ah T X c ω})
  have hGm : MeasurableSet G := measurableSet_FinGood.inter
    ((measurableSet_le hT (measurable_arrival j)).inter
      (measurableSet_lt (measurable_arrival j) (measurable_nucG Ag Ah hT hX hX0 hc)))
  let B : Set (Omega D.M) := (fun ω => zs ω j) ⁻¹' G
  have hBm : MeasurableSet B := (measurable_zs j) hGm
  have hBinv : ∀ (ω : Omega D.M) (x : ℝ),
      ((ω.1, Function.update ω.2.1 j x, ω.2.2) : Omega D.M) ∈ B ↔ ω ∈ B := by
    intro ω x
    have : zs ((ω.1, Function.update ω.2.1 j x, ω.2.2) : Omega D.M) j = zs ω j := by
      simp only [zs, Function.update_idem]
    simp only [B, mem_preimage, this]
  have hcore := service_core D j B hBm hBinv
  have hae : ∀ᵐ ω ∂D.P, (ω ∈ B ↔ ω ∈ Eset T X Ag Ah c j) := by
    filter_upwards [hgood] with ω hG
    have hG' := FinGood_zs hG j
    simp only [B, G, Eset, mem_preimage, mem_inter_iff, mem_setOf_eq, nucG, if_pos hG', hTzs,
      hXzs, arrival_zs, hG', true_and]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, (nuc_lt_iff_zs hG j Ag Ah (T ω) (X ω) c hc h1).1 h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, (nuc_lt_iff_zs hG j Ag Ah (T ω) (X ω) c hc h1).2 h2⟩
  have hind : B.indicator (fun ω : Omega D.M => ENNReal.ofReal (ω.2.1 j)) =ᵐ[D.P]
      (Eset T X Ag Ah c j).indicator (fun ω => ENNReal.ofReal (ω.2.1 j)) := by
    filter_upwards [hae] with ω h
    by_cases hb : ω ∈ B
    · rw [indicator_of_mem hb, indicator_of_mem (h.1 hb)]
    · rw [indicator_of_notMem hb, indicator_of_notMem (fun he => hb (h.2 he))]
  have hmeasF : Measurable (B.indicator (fun ω : Omega D.M => ENNReal.ofReal (ω.2.1 j))) :=
    (ENNReal.measurable_ofReal.comp
      ((measurable_pi_apply j).comp (measurable_fst.comp measurable_snd))).indicator hBm
  refine ⟨?_, hmeasF.aemeasurable.congr hind⟩
  rw [← lintegral_congr_ae hind, hcore]
  exact measure_congr (Filter.eventuallyEq_set.2 hae)

/-- W3 summed over class `i`, combined with W2:
`μ_i E[work_i[T, nuc)] + λ_i E T = λ_i E nuc`. -/
theorem work_bp_class (D : Data) (i : Fin D.M) (Ag Ah : Job D.M → Prop) (T X : Omega D.M → ℝ)
    (hT : Measurable T) (hX : Measurable X) (hX0 : ∀ ω, FinGood ω → 0 ≤ X ω) {c : ℝ}
    (hc : 0 ≤ c) (hTzs : ∀ ω m, T (zs ω (i, m)) = T ω) (hXzs : ∀ ω m, X (zs ω (i, m)) = X ω)
    (hTinv : ∀ m ω x, T (upd ω i m x) = T ω) (hXinv : ∀ m ω x, X (upd ω i m x) = X ω)
    (hgood : ∀ᵐ ω ∂D.P, FinGood ω ∧ (∀ k, 0 ≤ ω.1 (i, k)) ∧ 0 ≤ T ω)
    (hwT : ENNReal.ofReal (D.lam i) * ∫⁻ ω, ENNReal.ofReal (T ω) ∂D.P =
      ∑' m, D.P {ω | arrival ω (i, m) < T ω}) :
    ENNReal.ofReal (D.mu i) * ∫⁻ ω, ∑' m, (Eset T X Ag Ah c (i, m)).indicator
        (fun ω => ENNReal.ofReal (ω.2.1 (i, m))) ω ∂D.P +
      ENNReal.ofReal (D.lam i) * ∫⁻ ω, ENNReal.ofReal (T ω) ∂D.P =
      ENNReal.ofReal (D.lam i) * ∫⁻ ω, ENNReal.ofReal (nuc ω Ag Ah (T ω) (X ω) c) ∂D.P := by
  have hs := fun m => service_bp D (i, m) Ag Ah T X hT hX hX0 hc (fun ω => hTzs ω m)
    (fun ω => hXzs ω m) (hgood.mono fun ω h => h.1)
  calc _ = ∑' m, D.P (Eset T X Ag Ah c (i, m)) + ∑' m, D.P {ω | arrival ω (i, m) < T ω} := by
        rw [lintegral_tsum (fun m => (hs m).2), ← ENNReal.tsum_mul_left, hwT]
        congr 1
        exact tsum_congr fun m => (hs m).1
    _ = ∑' m, D.P {ω | arrival ω (i, m) < nuc ω Ag Ah (T ω) (X ω) c} := by
        rw [← ENNReal.tsum_add]
        refine tsum_congr fun m => ?_
        rw [← measure_union ?_ (measurableSet_lt (measurable_arrival _) hT)]
        · congr 1
          ext ω
          have hTn : T ω ≤ nuc ω Ag Ah (T ω) (X ω) c := by
            unfold nuc
            linarith [bpc_nonneg (x := backlogA ω Ag (T ω) + X ω)
              (fun u => workA ω Ah (T ω) (T ω + u)) hc]
          simp only [Eset, mem_union, mem_setOf_eq]
          constructor
          · rintro (⟨_, h2⟩ | h)
            · exact h2
            · linarith
          · intro h
            by_cases h' : T ω ≤ arrival ω (i, m)
            · exact Or.inl ⟨h', h⟩
            · exact Or.inr (lt_of_not_ge h')
        · rw [Set.disjoint_left]
          rintro ω ⟨h1, _⟩ h2
          simp only [mem_setOf_eq] at h2
          linarith
    _ = _ := (wald_bp D i Ag Ah T X hT hX hX0 hTinv hXinv hc hgood).symm

/-- On a good path, the `h`-work arriving in `[T, nuc)` splits into the class sums of W3. -/
theorem ofReal_workA_split {ω : Omega M} (hG : FinGood ω) (h : Finset (Fin M))
    (Ag : Job M → Prop) (T X : Omega M → ℝ) (c : ℝ) :
    ENNReal.ofReal (workA ω (fun j => j.1 ∈ h) (T ω)
        (nuc ω Ag (fun j => j.1 ∈ h) (T ω) (X ω) c)) =
      ∑ i ∈ h, ∑' m, (Eset T X Ag (fun j => j.1 ∈ h) c (i, m)).indicator
        (fun ω => ENNReal.ofReal (ω.2.1 (i, m))) ω := by
  classical
  unfold workA
  rw [ENNReal.ofReal_tsum_of_nonneg (fun j => indicator_nonneg (fun q _ => hG.1 q) j)
    (workA_summable hG _ _ _), ENNReal.tsum_prod', tsum_fintype]
  rw [← Finset.sum_subset (Finset.subset_univ h) ?_]
  · refine Finset.sum_congr rfl (fun i hi => tsum_congr (fun m => ?_))
    by_cases hm : T ω ≤ arrival ω (i, m) ∧
        arrival ω (i, m) < nuc ω Ag (fun j => j.1 ∈ h) (T ω) (X ω) c
    · rw [indicator_of_mem (show ((i, m) : Job M) ∈ {j : Job M | j.1 ∈ h ∧ T ω ≤ arrival ω j ∧
          arrival ω j < nuc ω Ag (fun j => j.1 ∈ h) (T ω) (X ω) c} from ⟨hi, hm⟩),
        indicator_of_mem (show ω ∈ Eset T X Ag (fun j => j.1 ∈ h) c (i, m) from hm)]
      rfl
    · rw [indicator_of_notMem (fun h' => hm h'.2),
        indicator_of_notMem (show ω ∉ Eset T X Ag (fun j => j.1 ∈ h) c (i, m) from hm),
        ENNReal.ofReal_zero]
  · intro i _ hi
    exact ENNReal.tsum_eq_zero.2 (fun m => by
      rw [indicator_of_notMem (fun h' => hi h'.1), ENNReal.ofReal_zero])

/-- W3 + W2 over the classes `h`: `E[work_h[T, T + τ^c)] = ρ_h E[τ^c]` (ENNReal). -/
theorem work_bp (D : Data) (h : Finset (Fin D.M)) (Ag : Job D.M → Prop) (T X : Omega D.M → ℝ)
    (hT : Measurable T) (hX : Measurable X) (hX0 : ∀ ω, FinGood ω → 0 ≤ X ω) {c : ℝ}
    (hc : 0 ≤ c) (hTzs : ∀ ω (j : Job D.M), j.1 ∈ h → T (zs ω j) = T ω)
    (hXzs : ∀ ω (j : Job D.M), j.1 ∈ h → X (zs ω j) = X ω)
    (hTinv : ∀ i ∈ h, ∀ m ω x, T (upd ω i m x) = T ω)
    (hXinv : ∀ i ∈ h, ∀ m ω x, X (upd ω i m x) = X ω)
    (hgood : ∀ᵐ ω ∂D.P, FinGood ω ∧ (∀ j : Job D.M, 0 ≤ ω.1 j) ∧ 0 ≤ T ω)
    (hwT : ∀ i ∈ h, ENNReal.ofReal (D.lam i) * ∫⁻ ω, ENNReal.ofReal (T ω) ∂D.P =
      ∑' m, D.P {ω | arrival ω (i, m) < T ω})
    (hTfin : ∫⁻ ω, ENNReal.ofReal (T ω) ∂D.P ≠ ⊤) :
    ∫⁻ ω, ENNReal.ofReal (workA ω (fun j => j.1 ∈ h) (T ω)
        (nuc ω Ag (fun j => j.1 ∈ h) (T ω) (X ω) c)) ∂D.P =
      ENNReal.ofReal (∑ i ∈ h, D.lam i / D.mu i) * ∫⁻ ω, ENNReal.ofReal
        (bpc (backlogA ω Ag (T ω) + X ω) c
          (fun u => workA ω (fun j => j.1 ∈ h) (T ω) (T ω + u))) ∂D.P := by
  classical
  have hnuc : ∫⁻ ω, ENNReal.ofReal (nuc ω Ag (fun j => j.1 ∈ h) (T ω) (X ω) c) ∂D.P =
      ∫⁻ ω, ENNReal.ofReal (T ω) ∂D.P + ∫⁻ ω, ENNReal.ofReal (bpc (backlogA ω Ag (T ω) + X ω) c
          (fun u => workA ω (fun j => j.1 ∈ h) (T ω) (T ω + u))) ∂D.P := by
    rw [← lintegral_add_left (show Measurable fun ω => ENNReal.ofReal (T ω) from
      ENNReal.measurable_ofReal.comp hT)]
    refine lintegral_congr_ae (hgood.mono fun ω hω => ?_)
    exact ENNReal.ofReal_add hω.2.2 (bpc_nonneg _ hc)
  have hcls : ∀ i ∈ h, ∫⁻ ω, ∑' m, (Eset T X Ag (fun j => j.1 ∈ h) c (i, m)).indicator
        (fun ω => ENNReal.ofReal (ω.2.1 (i, m))) ω ∂D.P =
      ENNReal.ofReal (D.lam i / D.mu i) * ∫⁻ ω, ENNReal.ofReal
        (bpc (backlogA ω Ag (T ω) + X ω) c
          (fun u => workA ω (fun j => j.1 ∈ h) (T ω) (T ω + u))) ∂D.P := by
    intro i hi
    have e := work_bp_class D i Ag (fun j => j.1 ∈ h) T X hT hX hX0 hc
      (fun ω m => hTzs ω (i, m) hi) (fun ω m => hXzs ω (i, m) hi) (hTinv i hi) (hXinv i hi)
      (hgood.mono fun ω hω => ⟨hω.1, fun k => hω.2.1 (i, k), hω.2.2⟩) (hwT i hi)
    rw [hnuc, mul_add, add_comm (ENNReal.ofReal (D.lam i) * ∫⁻ ω, ENNReal.ofReal (T ω) ∂D.P)] at e
    have e2 := WithTop.add_right_cancel (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hTfin) e
    have hmu : 0 < D.mu i := D.mu_pos i
    have h0 : ENNReal.ofReal (D.mu i) ≠ 0 := by simpa using hmu
    rw [ENNReal.ofReal_div_of_pos hmu]
    calc _ = (ENNReal.ofReal (D.mu i))⁻¹ * (ENNReal.ofReal (D.mu i) *
          ∫⁻ ω, ∑' m, (Eset T X Ag (fun j => j.1 ∈ h) c (i, m)).indicator
            (fun ω => ENNReal.ofReal (ω.2.1 (i, m))) ω ∂D.P) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel h0 ENNReal.ofReal_ne_top, one_mul]
      _ = _ := by rw [e2, ENNReal.div_eq_inv_mul, mul_assoc]
  calc _ = ∫⁻ ω, ∑ i ∈ h, ∑' m, (Eset T X Ag (fun j => j.1 ∈ h) c (i, m)).indicator
        (fun ω => ENNReal.ofReal (ω.2.1 (i, m))) ω ∂D.P :=
        lintegral_congr_ae (hgood.mono fun ω hω => ofReal_workA_split hω.1 h Ag T X c)
    _ = ∑ i ∈ h, ∫⁻ ω, ∑' m, (Eset T X Ag (fun j => j.1 ∈ h) c (i, m)).indicator
        (fun ω => ENNReal.ofReal (ω.2.1 (i, m))) ω ∂D.P :=
        lintegral_finset_sum' h (fun i hi => AEMeasurable.ennreal_tsum (fun m =>
          (service_bp D (i, m) Ag (fun j => j.1 ∈ h) T X hT hX hX0 hc
            (fun ω => hTzs ω (i, m) hi) (fun ω => hXzs ω (i, m) hi)
            (hgood.mono fun ω hω => hω.1)).2))
    _ = _ := by
        rw [Finset.sum_congr rfl hcls, ← Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg
          (fun i _ => div_nonneg (D.lam_pos i).le (D.mu_pos i).le)]

theorem ennreal_le_alg {a b r : ENNReal} (ha : a ≠ ⊤) (h : a ≤ b + r * a) : a * (1 - r) ≤ b := by
  rw [ENNReal.mul_sub (fun _ _ => ha), mul_one, tsub_le_iff_right, mul_comm]; exact h

theorem ennreal_eq_alg {a b r : ENNReal} (ha : a ≠ ⊤) (hr : r ≠ ⊤) (h : a = b + r * a) :
    a * (1 - r) = b := by
  rw [ENNReal.mul_sub (fun _ _ => ha), mul_one, mul_comm]
  calc a - r * a = (b + r * a) - r * a := by rw [← h]
    _ = b := ENNReal.add_sub_cancel_right (ENNReal.mul_ne_top hr ha)

/-- D4: the capped delay busy period satisfies `E τ^c (1 - ρ_h) ≤ E x`. -/
theorem cap_bound (D : Data) (h : Finset (Fin D.M)) (Ag : Job D.M → Prop) (T X : Omega D.M → ℝ)
    (hT : Measurable T) (hX : Measurable X) (hX0 : ∀ ω, FinGood ω → 0 ≤ X ω) {c : ℝ}
    (hc : 0 ≤ c) (hTzs : ∀ ω (j : Job D.M), j.1 ∈ h → T (zs ω j) = T ω)
    (hXzs : ∀ ω (j : Job D.M), j.1 ∈ h → X (zs ω j) = X ω)
    (hTinv : ∀ i ∈ h, ∀ m ω x, T (upd ω i m x) = T ω)
    (hXinv : ∀ i ∈ h, ∀ m ω x, X (upd ω i m x) = X ω)
    (hgood : ∀ᵐ ω ∂D.P, FinGood ω ∧ (∀ j : Job D.M, 0 ≤ ω.1 j) ∧ 0 ≤ T ω)
    (hwT : ∀ i ∈ h, ENNReal.ofReal (D.lam i) * ∫⁻ ω, ENNReal.ofReal (T ω) ∂D.P =
      ∑' m, D.P {ω | arrival ω (i, m) < T ω})
    (hTfin : ∫⁻ ω, ENNReal.ofReal (T ω) ∂D.P ≠ ⊤)
    (hxm : AEMeasurable (fun ω => ENNReal.ofReal (backlogA ω Ag (T ω) + X ω)) D.P) :
    (∫⁻ ω, ENNReal.ofReal (bpc (backlogA ω Ag (T ω) + X ω) c
        (fun u => workA ω (fun j => j.1 ∈ h) (T ω) (T ω + u))) ∂D.P) *
      (1 - ENNReal.ofReal (∑ i ∈ h, D.lam i / D.mu i)) ≤
      ∫⁻ ω, ENNReal.ofReal (backlogA ω Ag (T ω) + X ω) ∂D.P := by
  haveI := P_isProb D
  have hle : ∫⁻ ω, ENNReal.ofReal (bpc (backlogA ω Ag (T ω) + X ω) c
        (fun u => workA ω (fun j => j.1 ∈ h) (T ω) (T ω + u))) ∂D.P ≤
      ∫⁻ ω, ENNReal.ofReal (backlogA ω Ag (T ω) + X ω) ∂D.P +
        ENNReal.ofReal (∑ i ∈ h, D.lam i / D.mu i) * ∫⁻ ω, ENNReal.ofReal
          (bpc (backlogA ω Ag (T ω) + X ω) c
            (fun u => workA ω (fun j => j.1 ∈ h) (T ω) (T ω + u))) ∂D.P := by
    rw [← work_bp D h Ag T X hT hX hX0 hc hTzs hXzs hTinv hXinv hgood hwT hTfin,
      ← lintegral_add_left' hxm]
    refine lintegral_mono_ae (hgood.mono fun ω hω => ?_)
    have hx0 : 0 ≤ backlogA ω Ag (T ω) + X ω :=
      add_nonneg (backlogA_nonneg ω _ _) (hX0 ω hω.1)
    show _ ≤ ENNReal.ofReal (backlogA ω Ag (T ω) + X ω) + ENNReal.ofReal
      (workA ω (fun j => j.1 ∈ h) (T ω) (nuc ω Ag (fun j => j.1 ∈ h) (T ω) (X ω) c))
    rw [← ENNReal.ofReal_add hx0 (workA_nonneg hω.1 _ _ _)]
    exact ENNReal.ofReal_le_ofReal (bpc_le_add hc hx0 (fun u => workA_nonneg hω.1 _ _ _)
      (workT_mono hω.1 _ _))
  have hfin : ∫⁻ ω, ENNReal.ofReal (bpc (backlogA ω Ag (T ω) + X ω) c
        (fun u => workA ω (fun j => j.1 ∈ h) (T ω) (T ω + u))) ∂D.P ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∫⁻ _ω, ENNReal.ofReal c ∂D.P) ?_
      (lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (bpc_le_c _ hc))
    rw [lintegral_const, measure_univ, mul_one]; exact ENNReal.ofReal_ne_top
  exact ennreal_le_alg hfin hle

/-- D5/D6: the uncapped delay busy period: `E τ (1 - ρ_h) = E x`, `E τ < ∞`. -/
theorem delay_mean (D : Data) (h : Finset (Fin D.M)) (Ag : Job D.M → Prop)
    (T X : Omega D.M → ℝ)
    (hT : Measurable T) (hX : Measurable X) (hX0 : ∀ ω, FinGood ω → 0 ≤ X ω)
    (hTzs : ∀ ω (j : Job D.M), j.1 ∈ h → T (zs ω j) = T ω)
    (hXzs : ∀ ω (j : Job D.M), j.1 ∈ h → X (zs ω j) = X ω)
    (hTinv : ∀ i ∈ h, ∀ m ω x, T (upd ω i m x) = T ω)
    (hXinv : ∀ i ∈ h, ∀ m ω x, X (upd ω i m x) = X ω)
    (hgood : ∀ᵐ ω ∂D.P, FinGood ω ∧ (∀ j : Job D.M, 0 ≤ ω.1 j) ∧ 0 ≤ T ω)
    (hwT : ∀ i ∈ h, ENNReal.ofReal (D.lam i) * ∫⁻ ω, ENNReal.ofReal (T ω) ∂D.P =
      ∑' m, D.P {ω | arrival ω (i, m) < T ω})
    (hTfin : ∫⁻ ω, ENNReal.ofReal (T ω) ∂D.P ≠ ⊤)
    (hxm : AEMeasurable (fun ω => ENNReal.ofReal (backlogA ω Ag (T ω) + X ω)) D.P)
    (hρ : ∑ i ∈ h, D.lam i / D.mu i < 1)
    (hxfin : ∫⁻ ω, ENNReal.ofReal (backlogA ω Ag (T ω) + X ω) ∂D.P ≠ ⊤) :
    (∫⁻ ω, ENNReal.ofReal (sInf {u : ℝ | 0 ≤ u ∧ backlogA ω Ag (T ω) + X ω +
        workA ω (fun j => j.1 ∈ h) (T ω) (T ω + u) ≤ u}) ∂D.P) *
      (1 - ENNReal.ofReal (∑ i ∈ h, D.lam i / D.mu i)) =
      ∫⁻ ω, ENNReal.ofReal (backlogA ω Ag (T ω) + X ω) ∂D.P ∧
    (∫⁻ ω, ENNReal.ofReal (sInf {u : ℝ | 0 ≤ u ∧ backlogA ω Ag (T ω) + X ω +
        workA ω (fun j => j.1 ∈ h) (T ω) (T ω + u) ≤ u}) ∂D.P) ≠ ⊤ ∧
    AEMeasurable (fun ω => ENNReal.ofReal (sInf {u : ℝ | 0 ≤ u ∧ backlogA ω Ag (T ω) + X ω +
        workA ω (fun j => j.1 ∈ h) (T ω) (T ω + u) ≤ u})) D.P := by
  classical
  set r := ENNReal.ofReal (∑ i ∈ h, D.lam i / D.mu i) with hr
  set A := ∫⁻ ω, ENNReal.ofReal (backlogA ω Ag (T ω) + X ω) ∂D.P with hA
  let xx : Omega D.M → ℝ := fun ω => backlogA ω Ag (T ω) + X ω
  let ww : Omega D.M → ℝ → ℝ := fun ω u => workA ω (fun j => j.1 ∈ h) (T ω) (T ω + u)
  let τN : ℕ → Omega D.M → ℝ := fun N ω => bpc (xx ω) N (ww ω)
  let τ : Omega D.M → ℝ := fun ω => sInf {u : ℝ | 0 ≤ u ∧ xx ω + ww ω u ≤ u}
  have hx0 : ∀ ω, FinGood ω → 0 ≤ xx ω := fun ω hω =>
    add_nonneg (backlogA_nonneg ω _ _) (hX0 ω hω)
  have hwm : ∀ ω, FinGood ω → Monotone (ww ω) := fun ω hω => workT_mono hω _ _
  have hw0 : ∀ ω, FinGood ω → ∀ u, 0 ≤ ww ω u := fun ω hω u => workA_nonneg hω _ _ _
  have hτ0 : ∀ ω, 0 ≤ τ ω := fun ω => Real.sInf_nonneg (fun u hu => hu.1)
  have P2 : ∀ ω, FinGood ω → ∀ N : ℕ, τN N ω < N →
      τN N ω ∈ {u : ℝ | 0 ≤ u ∧ xx ω + ww ω u ≤ u} ∧ τN N ω = τ ω ∧
        τ ω = xx ω + ww ω (τ ω) := by
    intro ω hω N hlt
    have hmem : τN N ω ∈ bpS (xx ω) N (ww ω) := bpc_mem (Nat.cast_nonneg N) (hwm ω hω)
    have hS : τN N ω ∈ {u : ℝ | 0 ≤ u ∧ xx ω + ww ω u ≤ u} :=
      ⟨hmem.1, hmem.2.resolve_right (not_le.2 hlt)⟩
    have he : τN N ω = τ ω := bpc_eq_sInf (Nat.cast_nonneg N) (hwm ω hω) ⟨_, hS⟩
      ((csInf_le ⟨0, fun u hu => hu.1⟩ hS).trans hlt.le)
    refine ⟨hS, he, ?_⟩
    rw [← he]
    exact bpc_eq_of_lt (Nat.cast_nonneg N) (hx0 ω hω) (hw0 ω hω) (hwm ω hω) hlt
  have hmono : ∀ ω, Monotone (fun N : ℕ => τN N ω) := fun ω a b hab =>
    bpc_mono_c (Nat.cast_nonneg a) (Nat.cast_le.2 hab)
  have P3 : ∀ ω, FinGood ω → ({u : ℝ | 0 ≤ u ∧ xx ω + ww ω u ≤ u}).Nonempty →
      ⨆ N : ℕ, ENNReal.ofReal (τN N ω) = ENNReal.ofReal (τ ω) := by
    intro ω hω hne
    have hN : ∀ N : ℕ, τ ω ≤ N → τN N ω = τ ω := fun N hN =>
      bpc_eq_sInf (Nat.cast_nonneg N) (hwm ω hω) hne hN
    obtain ⟨N0, hN0⟩ := exists_nat_ge (τ ω)
    refine le_antisymm (iSup_le fun N => ?_) (le_iSup_of_le N0 (by rw [hN N0 hN0]))
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← hN (max N N0) (le_trans hN0 (by exact_mod_cast le_max_right N N0))]
    exact hmono ω (le_max_left N N0)
  have hτNm : ∀ N : ℕ, AEMeasurable (fun ω => ENNReal.ofReal (τN N ω)) D.P := by
    intro N
    have hx0' : ∀ ω, FinGood ω → 0 ≤ backlogM ω Ag (T ω) + X ω := fun ω hω => by
      rw [backlogM_eq hω]; exact hx0 ω hω
    refine (ENNReal.measurable_ofReal.comp (measurable_bpcG (fun j : Job D.M => j.1 ∈ h)
      ((measurable_backlogM Ag hT).add hX) hT hx0' (Nat.cast_nonneg N))).aemeasurable.congr ?_
    filter_upwards [hgood] with ω hω
    show ENNReal.ofReal (if FinGood ω then bpc (backlogM ω Ag (T ω) + X ω) N
        (fun u => workA ω (fun j => j.1 ∈ h) (T ω) (T ω + u)) else 0) =
      ENNReal.ofReal (bpc (backlogA ω Ag (T ω) + X ω) N
        (fun u => workA ω (fun j => j.1 ∈ h) (T ω) (T ω + u)))
    rw [if_pos hω.1, backlogM_eq hω.1]
  have hcap : ∀ N : ℕ, (∫⁻ ω, ENNReal.ofReal (τN N ω) ∂D.P) * (1 - r) ≤ A := fun N =>
    cap_bound D h Ag T X hT hX hX0 (Nat.cast_nonneg N) hTzs hXzs hTinv hXinv hgood hwT hTfin hxm
  have hL : ∫⁻ ω, ⨆ N : ℕ, ENNReal.ofReal (τN N ω) ∂D.P =
      ⨆ N : ℕ, ∫⁻ ω, ENNReal.ofReal (τN N ω) ∂D.P :=
    lintegral_iSup' hτNm (Filter.Eventually.of_forall fun ω a b hab =>
      ENNReal.ofReal_le_ofReal (hmono ω hab))
  set L := ⨆ N : ℕ, ∫⁻ ω, ENNReal.ofReal (τN N ω) ∂D.P with hLdef
  have hr1 : 1 - r ≠ 0 := (tsub_pos_iff_lt.2 (ENNReal.ofReal_lt_one.2 hρ)).ne'
  have hLup : L * (1 - r) ≤ A := by
    rw [hLdef, ENNReal.iSup_mul]; exact iSup_le hcap
  have hLfin : L ≠ ⊤ := by
    have := (ENNReal.le_div_iff_mul_le (Or.inl hr1)
      (Or.inl (ENNReal.sub_ne_top ENNReal.one_ne_top))).2 hLup
    exact ne_top_of_le_ne_top (ENNReal.div_lt_top hxfin hr1).ne this
  have hsupfin : ∀ᵐ ω ∂D.P, ⨆ N : ℕ, ENNReal.ofReal (τN N ω) < ⊤ :=
    ae_lt_top' (AEMeasurable.iSup hτNm) (by rw [hL]; exact hLfin)
  have hfix : ∀ᵐ ω ∂D.P, ⨆ N : ℕ, ENNReal.ofReal (τN N ω) = ENNReal.ofReal (τ ω) ∧
      τ ω = xx ω + ww ω (τ ω) := by
    filter_upwards [hgood, hsupfin] with ω hω hfin
    obtain ⟨N, hN⟩ := exists_nat_gt (⨆ N : ℕ, ENNReal.ofReal (τN N ω)).toReal
    have hle : τN N ω ≤ (⨆ N : ℕ, ENNReal.ofReal (τN N ω)).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal hfin.ne).1
        (le_iSup (fun N => ENNReal.ofReal (τN N ω)) N)
    obtain ⟨hS, _, hfx⟩ := P2 ω hω.1 N (hle.trans_lt hN)
    exact ⟨P3 ω hω.1 ⟨_, hS⟩, hfx⟩
  have hEτ : ∫⁻ ω, ENNReal.ofReal (τ ω) ∂D.P = L := by
    exact (lintegral_congr_ae (hfix.mono fun ω h => h.1.symm)).trans hL
  have hlow : A + r * L ≤ L := by
    rw [hLdef, ENNReal.mul_iSup, ENNReal.add_iSup]
    refine iSup_le fun N => ?_
    rw [← work_bp D h Ag T X hT hX hX0 (Nat.cast_nonneg N) hTzs hXzs hTinv hXinv hgood hwT
      hTfin, hA, ← lintegral_add_left' hxm, ← hLdef, ← hEτ]
    refine lintegral_mono_ae ?_
    filter_upwards [hgood, hfix] with ω hω hf
    rw [← ENNReal.ofReal_add (hx0 ω hω.1) (workA_nonneg hω.1 _ _ _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hle : τN N ω ≤ τ ω := (ENNReal.ofReal_le_ofReal_iff (hτ0 ω)).1
      (hf.1 ▸ le_iSup (fun N => ENNReal.ofReal (τN N ω)) N)
    have h1 := hwm ω hω.1 hle
    show xx ω + ww ω (τN N ω) ≤ τ ω
    linarith [hf.2]
  have hupper : L ≤ A + r * L := by
    have := hLup
    rw [ENNReal.mul_sub (fun _ _ => hLfin), mul_one, tsub_le_iff_right, mul_comm] at this
    exact this
  have heq : L = A + r * L := le_antisymm hupper hlow
  have key : (∫⁻ ω, ENNReal.ofReal (τ ω) ∂D.P) * (1 - r) = A ∧
      ∫⁻ ω, ENNReal.ofReal (τ ω) ∂D.P ≠ ⊤ := by
    rw [hEτ]; exact ⟨ennreal_eq_alg hLfin ENNReal.ofReal_ne_top heq, hLfin⟩
  exact ⟨key.1, key.2, (AEMeasurable.iSup hτNm).congr (hfix.mono fun ω h => h.1)⟩

end CM4X

/-! 608dae3b relay 14: C2 assembly (exact per-n delay formula for class `c` behind the chain `g`). -/
namespace CM4Y
open MeasureTheory ProbabilityTheory Set CoffmanMitrani CM4B CM4T CM4M CM4W CM4V CM4Z CM4X

variable {M : ℕ}

def Tc (c : Fin M) (n : ℕ) : Omega M → ℝ := fun ω => arrival ω (c, n)

def Bset (T : Omega M → ℝ) (j : Job M) : Set (Omega M) :=
  {ω | 0 ≤ arrival ω j ∧ arrival ω j < T ω}

noncomputable def bC (ω : Omega M) (g : Finset (Fin M)) (c : Fin M) (n : ℕ) : ℝ :=
  backlogA ω (fun j => j.1 ∈ g) (arrival ω (c, n))

noncomputable def tauC (ω : Omega M) (g : Finset (Fin M)) (c : Fin M) (n : ℕ) : ℝ :=
  sInf {u : ℝ | 0 ≤ u ∧ backlogA ω (fun j => j.1 ∈ g) (arrival ω (c, n)) + serviceReq ω (c, n) +
    workA ω (fun j => j.1 ∈ g.erase c) (arrival ω (c, n)) (arrival ω (c, n) + u) ≤ u}

theorem ne_top_of_mul_ne_top' {a b : ENNReal} (ha : a ≠ 0) (h : a * b ≠ ⊤) : b ≠ ⊤ := by
  rintro rfl
  exact h (ENNReal.mul_top ha)

theorem ne_top_of_mul_eq_one {r : ℝ} (hr : 0 < r) {I : ENNReal}
    (h : ENNReal.ofReal r * I = 1) : I ≠ ⊤ :=
  ne_top_of_mul_ne_top' (ENNReal.ofReal_pos.2 hr).ne' (by rw [h]; exact ENNReal.one_ne_top)

theorem inter_mean (D : Data) (j : Job D.M) :
    ENNReal.ofReal (D.lam j.1) * ∫⁻ ω, ENNReal.ofReal (ω.1 j) ∂D.P = 1 := by
  haveI := P_isProb D
  haveI := isProbabilityMeasure_expMeasure (D.lam_pos j.1)
  have hm : Measurable (fun ω : Omega D.M => ENNReal.ofReal (ω.1 j)) :=
    ENNReal.measurable_ofReal.comp ((measurable_pi_apply j).comp measurable_fst)
  rw [← (P_resampleA D j).lintegral_comp hm]
  simp only [Function.update_self]
  rw [lintegral_prod (fun p : ℝ × Omega D.M => ENNReal.ofReal p.1)
    measurable_fst.ennreal_ofReal.aemeasurable]
  simp only [lintegral_const, measure_univ, mul_one]
  exact exp_mean_lintegral (D.lam_pos j.1)

theorem serv_mean (D : Data) (j : Job D.M) :
    ENNReal.ofReal (D.mu j.1) * ∫⁻ ω, ENNReal.ofReal (ω.2.1 j) ∂D.P = 1 := by
  haveI := P_isProb D
  have h := service_core D j univ MeasurableSet.univ (fun ω x => Iff.rfl)
  simpa [Set.indicator_univ] using h

theorem arr_fin (D : Data) (c : Fin D.M) (n : ℕ)
    (hgood : ∀ᵐ ω ∂D.P, FinGood ω ∧ ∀ j : Job D.M, 0 ≤ ω.1 j) :
    ∫⁻ ω, ENNReal.ofReal (arrival ω (c, n)) ∂D.P ≠ ⊤ := by
  have h1 : ∫⁻ ω, ENNReal.ofReal (arrival ω (c, n)) ∂D.P =
      ∫⁻ ω, ∑ k ∈ Finset.range (n + 1), ENNReal.ofReal (ω.1 (c, k)) ∂D.P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hgood] with ω hω
    exact ENNReal.ofReal_sum_of_nonneg (fun k _ => hω.2 (c, k))
  rw [h1, lintegral_finset_sum (Finset.range (n + 1)) (f := fun k (ω : Omega D.M) => ENNReal.ofReal (ω.1 (c, k)))
    (fun k _ => ((measurable_pi_apply (c, k)).comp measurable_fst).ennreal_ofReal)]
  exact ENNReal.sum_ne_top.2 (fun k _ => ne_top_of_mul_eq_one (D.lam_pos c) (inter_mean D (c, k)))

theorem exists_arr_ge {ω : Omega M} (hG : FinGood ω) (i : Fin M) (t : ℝ) :
    ∃ N, t ≤ ∑ k ∈ Finset.range (N + 1), ω.1 (i, k) := by
  by_contra hcon
  push_neg at hcon
  exact Set.infinite_of_injective_forall_mem (f := fun N : ℕ => ((i, N) : Job M))
    (fun a b hab => congrArg Prod.snd hab) (fun N => (hcon N : arrival ω (i, N) < t)) (hG.2 t)

theorem hwT_arr (D : Data) (c i : Fin D.M) (hic : i ≠ c) (n : ℕ)
    (hgood : ∀ᵐ ω ∂D.P, FinGood ω ∧ ∀ j : Job D.M, 0 ≤ ω.1 j) :
    ENNReal.ofReal (D.lam i) * ∫⁻ ω, ENNReal.ofReal (arrival ω (c, n)) ∂D.P =
      ∑' m, D.P {ω | arrival ω (i, m) < arrival ω (c, n)} := by
  have hT0 : ∀ᵐ ω ∂D.P, max 0 (∑ k ∈ Finset.range (n + 1), ω.1 (c, k)) = arrival ω (c, n) := by
    filter_upwards [hgood] with ω hω
    exact max_eq_right (Finset.sum_nonneg fun k _ => hω.2 (c, k))
  have hw := wald_arrival D i c hic n (hgood.mono fun ω h k => h.2 (i, k))
    (hgood.mono fun ω h => exists_arr_ge h.1 i _)
  have hL : ∫⁻ ω, ENNReal.ofReal (max 0 (∑ k ∈ Finset.range (n + 1), ω.1 (c, k))) ∂D.P =
      ∫⁻ ω, ENNReal.ofReal (arrival ω (c, n)) ∂D.P :=
    lintegral_congr_ae (hT0.mono fun ω h => congrArg ENNReal.ofReal h)
  rw [hL] at hw
  rw [hw]
  refine tsum_congr fun m => measure_congr ?_
  filter_upwards [hT0] with ω hω
  show (_ < _) = (_ < _)
  rw [hω]
  rfl

theorem backlog_le_work {ω : Omega M} (hG : FinGood ω) (A : Job M → Prop) (t : ℝ) :
    backlogA ω A t ≤ workA ω A 0 t := by
  rw [backlogA_eq_iSup hG]
  exact Real.iSup_le (fun q => bq_le hG A t q) (workA_nonneg hG A 0 t)

theorem ofReal_work0_split {ω : Omega M} (hG : FinGood ω) (g : Finset (Fin M))
    (T : Omega M → ℝ) :
    ENNReal.ofReal (workA ω (fun j => j.1 ∈ g) 0 (T ω)) =
      ∑ i ∈ g, ∑' m, (Bset T (i, m)).indicator (fun ω => ENNReal.ofReal (ω.2.1 (i, m))) ω := by
  classical
  unfold workA
  rw [ENNReal.ofReal_tsum_of_nonneg (fun j => indicator_nonneg (fun q _ => hG.1 q) j)
    (workA_summable hG _ _ _), ENNReal.tsum_prod', tsum_fintype]
  rw [← Finset.sum_subset (Finset.subset_univ g) ?_]
  · refine Finset.sum_congr rfl (fun i hi => tsum_congr (fun m => ?_))
    by_cases hm : 0 ≤ arrival ω (i, m) ∧ arrival ω (i, m) < T ω
    · rw [indicator_of_mem (show ((i, m) : Job M) ∈ {j : Job M | j.1 ∈ g ∧ 0 ≤ arrival ω j ∧
          arrival ω j < T ω} from ⟨hi, hm⟩),
        indicator_of_mem (show ω ∈ Bset T (i, m) from hm)]
      rfl
    · rw [indicator_of_notMem (fun h' => hm h'.2),
        indicator_of_notMem (show ω ∉ Bset T (i, m) from hm), ENNReal.ofReal_zero]
  · intro i _ hi
    exact ENNReal.tsum_eq_zero.2 (fun m => by
      rw [indicator_of_notMem (fun h' => hi h'.1), ENNReal.ofReal_zero])

theorem serv_B (D : Data) (j : Job D.M) {T : Omega D.M → ℝ} (hT : Measurable T)
    (hTs : ∀ (ω : Omega D.M) (x : ℝ),
      T ((ω.1, Function.update ω.2.1 j x, ω.2.2) : Omega D.M) = T ω) :
    ENNReal.ofReal (D.mu j.1) * ∫⁻ ω, (Bset T j).indicator
      (fun ω => ENNReal.ofReal (ω.2.1 j)) ω ∂D.P = D.P (Bset T j) :=
  service_core D j (Bset T j) ((measurableSet_le measurable_const (measurable_arrival j)).inter
    (measurableSet_lt (measurable_arrival j) hT))
    (fun ω x => Iff.of_eq (congrArg (fun t => 0 ≤ arrival ω j ∧ arrival ω j < t) (hTs ω x)))

theorem own_class_le (D : Data) (c : Fin D.M) (n m : ℕ)
    (hgood : ∀ᵐ ω ∂D.P, FinGood ω ∧ ∀ j : Job D.M, 0 ≤ ω.1 j) :
    D.P {ω | arrival ω (c, m) < arrival ω (c, n)} ≤ if m < n then 1 else 0 := by
  haveI := P_isProb D
  split_ifs with hmn
  · exact prob_le_one
  · refine le_of_eq (measure_mono_null ?_ (ae_iff.1 hgood))
    intro ω hω
    simp only [mem_setOf_eq]
    intro hgω
    have h1 : arrival ω (c, n) ≤ arrival ω (c, m) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
        (fun k _ _ => hgω.2 (c, k))
    exact absurd hω (not_lt.2 h1)

theorem own_class_fin (D : Data) (c : Fin D.M) (n : ℕ)
    (hgood : ∀ᵐ ω ∂D.P, FinGood ω ∧ ∀ j : Job D.M, 0 ≤ ω.1 j) :
    ∑' m, D.P {ω | arrival ω (c, m) < arrival ω (c, n)} ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun m => own_class_le D c n m hgood)
  rw [tsum_eq_sum (s := Finset.range n) (fun m hm => if_neg (fun h => hm (Finset.mem_range.2 h)))]
  exact ENNReal.sum_ne_top.2 (fun m _ => by split_ifs <;> simp)

theorem backlog_fin (D : Data) (g : Finset (Fin D.M)) (c : Fin D.M) (n : ℕ)
    (hgood : ∀ᵐ ω ∂D.P, FinGood ω ∧ ∀ j : Job D.M, 0 ≤ ω.1 j) :
    ∫⁻ ω, ENNReal.ofReal (bC ω g c n) ∂D.P ≠ ⊤ := by
  classical
  haveI := P_isProb D
  have hT : Measurable (Tc c n : Omega D.M → ℝ) := measurable_arrival (c, n)
  have hB : ∀ j : Job D.M, MeasurableSet (Bset (Tc c n) j) := fun j =>
    (measurableSet_le measurable_const (measurable_arrival j)).inter
      (measurableSet_lt (measurable_arrival j) hT)
  have hIm : ∀ j : Job D.M, Measurable ((Bset (Tc c n) j).indicator
      (fun ω : Omega D.M => ENNReal.ofReal (ω.2.1 j))) := fun j =>
    (ENNReal.measurable_ofReal.comp ((measurable_pi_apply j).comp
      (measurable_fst.comp measurable_snd))).indicator (hB j)
  have hle : ∫⁻ ω, ENNReal.ofReal (bC ω g c n) ∂D.P ≤
      ∑ i ∈ g, ∑' m, ∫⁻ ω, (Bset (Tc c n) (i, m)).indicator
        (fun ω => ENNReal.ofReal (ω.2.1 (i, m))) ω ∂D.P := by
    calc _ ≤ ∫⁻ ω, ∑ i ∈ g, ∑' m, (Bset (Tc c n) (i, m)).indicator
          (fun ω => ENNReal.ofReal (ω.2.1 (i, m))) ω ∂D.P := by
          refine lintegral_mono_ae ?_
          filter_upwards [hgood] with ω hω
          exact (ENNReal.ofReal_le_ofReal (backlog_le_work hω.1 _ _)).trans
            (le_of_eq (ofReal_work0_split hω.1 g (Tc c n)))
      _ = _ := by
          rw [lintegral_finset_sum _ (fun i _ => Measurable.ennreal_tsum fun m => hIm (i, m))]
          exact Finset.sum_congr rfl fun i _ => lintegral_tsum fun m => (hIm (i, m)).aemeasurable
  have hcls : ∀ i, ∑' m, D.P {ω | arrival ω (i, m) < arrival ω (c, n)} ≠ ⊤ := by
    intro i
    by_cases hic : i = c
    · rw [hic]; exact own_class_fin D c n hgood
    · rw [← hwT_arr D c i hic n hgood]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (arr_fin D c n hgood)
  refine ne_top_of_le_ne_top (ENNReal.sum_ne_top.2 fun i _ => ?_) hle
  refine ne_top_of_mul_ne_top' (ENNReal.ofReal_pos.2 (D.mu_pos i)).ne' ?_
  rw [← ENNReal.tsum_mul_left]
  have heq : ∑' m, ENNReal.ofReal (D.mu i) * ∫⁻ ω, (Bset (Tc c n) (i, m)).indicator
      (fun ω => ENNReal.ofReal (ω.2.1 (i, m))) ω ∂D.P = ∑' m, D.P (Bset (Tc c n) (i, m)) :=
    tsum_congr fun m => serv_B D (i, m) hT (fun ω x => rfl)
  rw [heq]
  exact ne_top_of_le_ne_top (hcls i) (ENNReal.tsum_le_tsum fun m => measure_mono fun ω hω => hω.2)

/-- **C2 (exact per n).** `E τ_n = (E backlog_g(T_n) + 1/μ_c) / (1 - ρ_{g∖c})`. -/
theorem C2_formula (D : Data) (g : Finset (Fin D.M)) (c : Fin D.M) (n : ℕ)
    (hgood : ∀ᵐ ω ∂D.P, FinGood ω ∧ ∀ j : Job D.M, 0 ≤ ω.1 j) :
    ∫ ω, tauC ω g c n ∂D.P = ((∫ ω, bC ω g c n ∂D.P) + 1 / D.mu c) /
      (1 - ∑ i ∈ g.erase c, D.lam i / D.mu i) := by
  classical
  haveI := P_isProb D
  have hT : Measurable (fun ω : Omega D.M => arrival ω (c, n)) := measurable_arrival (c, n)
  have hX : Measurable (fun ω : Omega D.M => serviceReq ω (c, n)) := measurable_serviceReq (c, n)
  have hic : ∀ i ∈ g.erase c, i ≠ c := fun i hi => Finset.ne_of_mem_erase hi
  have hgood' : ∀ᵐ ω ∂D.P, FinGood ω ∧ (∀ j : Job D.M, 0 ≤ ω.1 j) ∧ 0 ≤ arrival ω (c, n) := by
    filter_upwards [hgood] with ω hω
    exact ⟨hω.1, hω.2, Finset.sum_nonneg fun k _ => hω.2 (c, k)⟩
  have hρ : ∑ i ∈ g.erase c, D.lam i / D.mu i < 1 :=
    lt_of_le_of_lt (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => div_nonneg (D.lam_pos i).le (D.mu_pos i).le)) D.stable
  have hρ0 : 0 ≤ ∑ i ∈ g.erase c, D.lam i / D.mu i :=
    Finset.sum_nonneg fun i _ => div_nonneg (D.lam_pos i).le (D.mu_pos i).le
  have hBm : AEMeasurable (fun ω => bC ω g c n) D.P :=
    (measurable_backlogM (fun j : Job D.M => j.1 ∈ g) hT).aemeasurable.congr
      (hgood.mono fun ω hω => backlogM_eq hω.1 (fun j : Job D.M => j.1 ∈ g) (arrival ω (c, n)))
  have hXm : AEMeasurable (fun ω => ENNReal.ofReal (serviceReq ω (c, n))) D.P :=
    (ENNReal.measurable_ofReal.comp hX).aemeasurable
  have hBfin : ∫⁻ ω, ENNReal.ofReal (bC ω g c n) ∂D.P ≠ ⊤ := backlog_fin D g c n hgood
  have hXmean : ENNReal.ofReal (D.mu c) * ∫⁻ ω, ENNReal.ofReal (serviceReq ω (c, n)) ∂D.P = 1 :=
    serv_mean D (c, n)
  have hXfin := ne_top_of_mul_eq_one (D.mu_pos c) hXmean
  have hsplit : ∫⁻ ω, ENNReal.ofReal (bC ω g c n + serviceReq ω (c, n)) ∂D.P =
      ∫⁻ ω, ENNReal.ofReal (bC ω g c n) ∂D.P +
        ∫⁻ ω, ENNReal.ofReal (serviceReq ω (c, n)) ∂D.P := by
    rw [← lintegral_add_right' (fun ω => ENNReal.ofReal (bC ω g c n)) hXm]
    refine lintegral_congr_ae ?_
    filter_upwards [hgood] with ω hω
    exact ENNReal.ofReal_add (backlogA_nonneg ω _ _) (hω.1.1 _)
  have hxm : AEMeasurable (fun ω => ENNReal.ofReal (bC ω g c n + serviceReq ω (c, n))) D.P :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hBm.add hX.aemeasurable)
  have hxfin : ∫⁻ ω, ENNReal.ofReal (bC ω g c n + serviceReq ω (c, n)) ∂D.P ≠ ⊤ := by
    rw [hsplit]; exact ENNReal.add_ne_top.2 ⟨hBfin, hXfin⟩
  have hall := delay_mean D (g.erase c) (fun j => j.1 ∈ g) (fun ω => arrival ω (c, n))
    (fun ω => serviceReq ω (c, n)) hT hX (fun ω hω => hω.1 _) (fun ω j _ => rfl)
    (fun ω j hj => serviceReq_zs_ne ω (fun hq => Finset.notMem_erase c g (by
      rw [← hq] at hj; exact hj)))
    (fun i hi m ω x => arrival_upd_of (ω := ω) (i := i) (m := m) (x := x) (q := (c, n))
      (fun h => absurd h.symm (hic i hi)))
    (fun _ _ _ _ _ => rfl) hgood' (fun i hi => hwT_arr D c i (hic i hi) n hgood)
    (arr_fin D c n hgood) hxm hρ hxfin
  have heq : (∫⁻ ω, ENNReal.ofReal (tauC ω g c n) ∂D.P) *
      (1 - ENNReal.ofReal (∑ i ∈ g.erase c, D.lam i / D.mu i)) =
      ∫⁻ ω, ENNReal.ofReal (bC ω g c n + serviceReq ω (c, n)) ∂D.P := hall.1
  have hτm : AEMeasurable (fun ω => ENNReal.ofReal (tauC ω g c n)) D.P := hall.2.2
  have hτ0 : ∀ ω, 0 ≤ tauC ω g c n := fun ω => Real.sInf_nonneg (fun u hu => hu.1)
  have hτm' : AEMeasurable (fun ω => tauC ω g c n) D.P :=
    (ENNReal.measurable_toReal.comp_aemeasurable hτm).congr
      (Filter.Eventually.of_forall fun ω => ENNReal.toReal_ofReal (hτ0 ω))
  have hIτ : ∫ ω, tauC ω g c n ∂D.P = (∫⁻ ω, ENNReal.ofReal (tauC ω g c n) ∂D.P).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hτ0) hτm'.aestronglyMeasurable
  have hIb : ∫ ω, bC ω g c n ∂D.P = (∫⁻ ω, ENNReal.ofReal (bC ω g c n) ∂D.P).toReal :=
    integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun ω => backlogA_nonneg ω _ _) hBm.aestronglyMeasurable
  have hXr : (∫⁻ ω, ENNReal.ofReal (serviceReq ω (c, n)) ∂D.P).toReal = 1 / D.mu c := by
    have h1 := congrArg ENNReal.toReal hXmean
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (D.mu_pos c).le, ENNReal.toReal_one] at h1
    rw [eq_div_iff (D.mu_pos c).ne', mul_comm]
    exact h1
  have hr1 : (1 - ENNReal.ofReal (∑ i ∈ g.erase c, D.lam i / D.mu i)).toReal =
      1 - ∑ i ∈ g.erase c, D.lam i / D.mu i := by
    rw [ENNReal.toReal_sub_of_le (ENNReal.ofReal_le_one.2 hρ.le) ENNReal.one_ne_top,
      ENNReal.toReal_one, ENNReal.toReal_ofReal hρ0]
  have key := congrArg ENNReal.toReal heq
  rw [hsplit, ENNReal.toReal_mul, ENNReal.toReal_add hBfin hXfin, hr1, hXr] at key
  rw [hIτ, hIb, eq_div_iff (by linarith)]
  exact key

end CM4Y

/-! relay 14: a.e. goodness (copied from 608dae3b_asm_ps.lean C1a) and the unconditional C2. -/
namespace CM4G
open CoffmanMitrani MeasureTheory ProbabilityTheory Filter Topology CM4W

theorem ae_interarrival_pos (D : Data) : ∀ᵐ ω ∂D.P, ∀ j : Job D.M, 0 < ω.1 j := by
  rw [ae_all_iff]
  intro j
  haveI : ∀ j : Job D.M, IsProbabilityMeasure (expMeasure (D.lam j.1)) :=
    fun j => isProbabilityMeasure_expMeasure (D.lam_pos j.1)
  haveI : ∀ j : Job D.M, IsProbabilityMeasure (expMeasure (D.mu j.1)) :=
    fun j => isProbabilityMeasure_expMeasure (D.mu_pos j.1)
  have hmeas : Measurable fun ω : Omega D.M => ω.1 j :=
    (measurable_pi_apply j).comp measurable_fst
  have hmap : D.P.map (fun ω : Omega D.M => ω.1 j) = expMeasure (D.lam j.1) := by
    have : (fun ω : Omega D.M => ω.1 j) = (fun x : Job D.M → ℝ => x j) ∘ Prod.fst := rfl
    rw [this, ← Measure.map_map (measurable_pi_apply j) measurable_fst]
    unfold Data.P
    rw [Measure.map_fst_prod, measure_univ, one_smul, Measure.infinitePi_map_eval]
  have h := expMeasure_ae_pos (D.lam_pos j.1)
  rw [← hmap] at h
  exact ae_of_ae_map hmeas.aemeasurable h

theorem ae_service_pos (D : Data) : ∀ᵐ ω ∂D.P, ∀ j : Job D.M, 0 < ω.2.1 j := by
  rw [ae_all_iff]
  intro j
  haveI : ∀ j : Job D.M, IsProbabilityMeasure (expMeasure (D.lam j.1)) :=
    fun j => isProbabilityMeasure_expMeasure (D.lam_pos j.1)
  haveI : ∀ j : Job D.M, IsProbabilityMeasure (expMeasure (D.mu j.1)) :=
    fun j => isProbabilityMeasure_expMeasure (D.mu_pos j.1)
  have hmeas : Measurable fun ω : Omega D.M => ω.2.1 j :=
    (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)
  have hmap : D.P.map (fun ω : Omega D.M => ω.2.1 j) = expMeasure (D.mu j.1) := by
    have : (fun ω : Omega D.M => ω.2.1 j) =
        (fun x : Job D.M → ℝ => x j) ∘ Prod.fst ∘ Prod.snd := rfl
    rw [this, ← Measure.map_map (measurable_pi_apply j) (measurable_fst.comp measurable_snd),
      ← Measure.map_map measurable_fst measurable_snd]
    unfold Data.P
    rw [Measure.map_snd_prod, measure_univ, one_smul, Measure.map_fst_prod, measure_univ,
      one_smul, Measure.infinitePi_map_eval]
  have h := expMeasure_ae_pos (D.mu_pos j.1)
  rw [← hmap] at h
  exact ae_of_ae_map hmeas.aemeasurable h

theorem tendsto_partial_sum_of_frequently {x : ℕ → ℝ} (hpos : ∀ m, 0 ≤ x m)
    (hfr : ∃ᶠ m in atTop, 1 ≤ x m) :
    Tendsto (fun n => ∑ m ∈ Finset.range (n + 1), x m) atTop atTop := by
  apply tendsto_atTop_atTop_of_monotone'
  · intro a b hab
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      (fun m _ _ => hpos m)
  · rintro ⟨B, hB⟩
    have hinf : Set.Infinite {m | 1 ≤ x m} := Nat.frequently_atTop_iff_infinite.1 hfr
    obtain ⟨t, hts, htc⟩ := hinf.exists_subset_card_eq (⌈B⌉₊ + 1)
    have hsub : t ⊆ Finset.range (t.sup id + 1) := fun m hm =>
      Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := id) hm))
    have h1 : ∑ m ∈ t, x m ≤ ∑ m ∈ Finset.range (t.sup id + 1), x m :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => hpos m)
    have h2 := Finset.card_nsmul_le_sum t x 1 (fun m hm => hts hm)
    rw [nsmul_one, htc] at h2
    have h3 := hB ⟨t.sup id, rfl⟩
    push_cast at h2
    linarith [Nat.le_ceil B]

theorem finite_le_of_tendsto {f : ℕ → ℝ} (hf : Tendsto f atTop atTop) (T : ℝ) :
    Set.Finite {n | f n ≤ T} := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hf.eventually_gt_atTop T)
  refine (Set.finite_lt_nat N).subset fun n hn => ?_
  by_contra h
  simp only [Set.mem_setOf_eq, not_lt] at h hn
  linarith [hN n h]

theorem jobs_finite_of_tendsto {M : ℕ} (ω : Omega M)
    (h : ∀ i : Fin M, Tendsto (fun n => arrival ω (i, n)) atTop atTop) (T : ℝ) :
    Set.Finite {j : Job M | arrival ω j ≤ T} := by
  have hsub : {j : Job M | arrival ω j ≤ T} ⊆
      ⋃ i : Fin M, (fun n => (i, n)) '' {n | arrival ω (i, n) ≤ T} := by
    rintro ⟨i, n⟩ hj
    exact Set.mem_iUnion.2 ⟨i, n, hj, rfl⟩
  exact (Set.finite_iUnion fun i => (finite_le_of_tendsto (h i) T).image _).subset hsub

theorem expMeasure_Ici_one_ne_zero {r : ℝ} (hr : 0 < r) : expMeasure r (Set.Ici 1) ≠ 0 := by
  haveI := isProbabilityMeasure_expMeasure hr
  intro h0
  have hle : expMeasure r (Set.Ioi 1) = 0 := measure_mono_null Set.Ioi_subset_Ici_self h0
  rw [← Set.compl_Iic, prob_compl_eq_zero_iff measurableSet_Iic, ← ofReal_cdf,
    cdf_expMeasure_eq hr] at hle
  simp only [zero_le_one, if_true, mul_one] at hle
  have hexp := Real.exp_pos (-r)
  have := (ENNReal.ofReal_eq_one).1 hle
  linarith

/-- Second Borel-Cantelli: a.s. infinitely many interarrival times of class `i` are `≥ 1`. -/
theorem ae_frequently_ge_one (D : Data) (i : Fin D.M) :
    ∀ᵐ ω ∂D.P, ∃ᶠ m in atTop, 1 ≤ ω.1 (i, m) := by
  haveI : ∀ j : Job D.M, IsProbabilityMeasure (expMeasure (D.lam j.1)) :=
    fun j => isProbabilityMeasure_expMeasure (D.lam_pos j.1)
  haveI : ∀ j : Job D.M, IsProbabilityMeasure (expMeasure (D.mu j.1)) :=
    fun j => isProbabilityMeasure_expMeasure (D.mu_pos j.1)
  set μ0 : Measure (Job D.M → ℝ) := Measure.infinitePi fun j : Job D.M => expMeasure (D.lam j.1)
    with hμ0
  have hmap : D.P.map Prod.fst = μ0 := by
    unfold Data.P
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  set s : ℕ → Set (Job D.M → ℝ) := fun m => (fun x => x (i, m)) ⁻¹' Set.Ici 1 with hs
  have hsm : ∀ m, MeasurableSet (s m) := fun m => measurable_pi_apply _ measurableSet_Ici
  have hF : iIndepFun (fun m (x : Job D.M → ℝ) => x (i, m)) μ0 := by
    have h0 := iIndepFun_infinitePi (P := fun j : Job D.M => expMeasure (D.lam j.1))
      (X := fun _ (y : ℝ) => y) (fun _ => measurable_id)
    exact h0.precomp (g := fun m : ℕ => (i, m)) (fun a b h => (Prod.ext_iff.1 h).2)
  have hind : iIndepSet s μ0 := by
    rw [iIndepSet_iff_meas_biInter hsm]
    intro S
    exact (iIndepFun_iff_measure_inter_preimage_eq_mul.1 hF) S
      (sets := fun _ => Set.Ici 1) (fun _ _ => measurableSet_Ici)
  have hval : ∀ m, μ0 (s m) = expMeasure (D.lam i) (Set.Ici 1) := by
    intro m
    rw [hs, ← Measure.map_apply (measurable_pi_apply _) measurableSet_Ici, hμ0,
      Measure.infinitePi_map_eval]
  have hsum : (∑' m, μ0 (s m)) = ⊤ := by
    simp_rw [hval]
    exact ENNReal.tsum_const_eq_top_of_ne_zero (expMeasure_Ici_one_ne_zero (D.lam_pos i))
  have hls := measure_limsup_eq_one hsm hind hsum
  have hLm : MeasurableSet (limsup s atTop) := by
    rw [Filter.limsup_eq_iInf_iSup_of_nat]
    exact MeasurableSet.iInter fun n => MeasurableSet.iUnion fun k =>
      MeasurableSet.iUnion fun _ => hsm k
  have hae : ∀ᵐ x ∂μ0, ∃ᶠ m in atTop, 1 ≤ x (i, m) := by
    rw [ae_iff]
    have : {a : Job D.M → ℝ | ¬ ∃ᶠ m in atTop, 1 ≤ a (i, m)} = (limsup s atTop)ᶜ := by
      ext a
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, mem_limsup_iff_frequently_mem, hs,
        Set.mem_preimage, Set.mem_Ici]
    rw [this, prob_compl_eq_zero_iff hLm]
    exact hls
  rw [← hmap] at hae
  exact ae_of_ae_map measurable_fst.aemeasurable hae

theorem ae_arrival_tendsto (D : Data) :
    ∀ᵐ ω ∂D.P, ∀ i : Fin D.M, Tendsto (fun n => arrival ω (i, n)) atTop atTop := by
  rw [ae_all_iff]
  intro i
  filter_upwards [ae_frequently_ge_one D i, ae_interarrival_pos D] with ω h1 h2
  exact tendsto_partial_sum_of_frequently (fun m => (h2 (i, m)).le) h1

theorem ae_arrival_finite (D : Data) :
    ∀ᵐ ω ∂D.P, ∀ T : ℝ, Set.Finite {j : Job D.M | arrival ω j ≤ T} := by
  filter_upwards [ae_arrival_tendsto D] with ω h T using jobs_finite_of_tendsto ω h T

theorem ae_good (D : Data) : ∀ᵐ ω ∂D.P, CM4T.FinGood ω ∧ ∀ j : Job D.M, 0 ≤ ω.1 j := by
  filter_upwards [ae_interarrival_pos D, ae_service_pos D, ae_arrival_finite D] with ω h1 h2 h3
  exact ⟨⟨fun q => (h2 q).le, fun t => (h3 t).subset fun q (hq : arrival ω q < t) => (le_of_lt hq : arrival ω q ≤ t)⟩, fun j => (h1 j).le⟩

/-- **C2, unconditional.** -/
theorem C2_exact (D : Data) (g : Finset (Fin D.M)) (c : Fin D.M) (n : ℕ) :
    ∫ ω, CM4Y.tauC ω g c n ∂D.P = ((∫ ω, CM4Y.bC ω g c n ∂D.P) + 1 / D.mu c) /
      (1 - ∑ i ∈ g.erase c, D.lam i / D.mu i) :=
  CM4Y.C2_formula D g c n (ae_good D)

end CM4G


namespace CM4C3
open MeasureTheory ProbabilityTheory Real Set

/-- `P(e > s) = e^{-r s}` (ENNReal form). -/
theorem expMeasure_Ioi {r : ℝ} (hr : 0 < r) {s : ℝ} (hs : 0 ≤ s) :
    expMeasure r (Ioi s) = ENNReal.ofReal (exp (-(r * s))) := by
  haveI := isProbabilityMeasure_expMeasure hr
  have h0 : 0 ≤ 1 - exp (-(r * s)) :=
    sub_nonneg.2 (Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hr.le hs)))
  rw [← compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, ← ofReal_cdf, cdf_expMeasure_eq hr,
    if_pos hs, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ h0]
  congr 1
  ring

/-- **S0 weighted exponential core** (general support set `S ⊆ [0,∞)`):
`r E ∫_{S ∩ [0,e)} φ = E[φ(e); e ∈ S]`. -/
theorem exp_weighted_set {r : ℝ} (hr : 0 < r) (φ : ℝ → ENNReal) (hφ : Measurable φ)
    {S : Set ℝ} (hS : MeasurableSet S) (hS0 : S ⊆ Ici 0) :
    ENNReal.ofReal r * ∫⁻ e, (∫⁻ s in S, (Iio e).indicator φ s) ∂(expMeasure r) =
      ∫⁻ e, S.indicator φ e ∂(expMeasure r) := by
  haveI := isProbabilityMeasure_expMeasure hr
  have hF : Measurable (Function.uncurry fun (e s : ℝ) => S.indicator
      ((Iio e).indicator φ) s) := by
    have hm : MeasurableSet {p : ℝ × ℝ | p.2 ∈ S ∧ p.2 < p.1} :=
      ((measurable_snd hS)).inter (measurableSet_lt measurable_snd measurable_fst)
    have heq : (Function.uncurry fun (e s : ℝ) => S.indicator ((Iio e).indicator φ) s) =
        {p : ℝ × ℝ | p.2 ∈ S ∧ p.2 < p.1}.indicator (φ ∘ Prod.snd) := by
      funext p
      simp only [Function.uncurry, Set.indicator, mem_setOf_eq, mem_Iio, Function.comp]
      by_cases h1 : p.2 ∈ S <;> by_cases h2 : p.2 < p.1 <;> simp [h1, h2]
    rw [heq]
    exact (hφ.comp measurable_snd).indicator hm
  have hswap : ∫⁻ e, (∫⁻ s in S, (Iio e).indicator φ s) ∂(expMeasure r) =
      ∫⁻ s in S, φ s * ENNReal.ofReal (exp (-(r * s))) := by
    simp_rw [← lintegral_indicator hS]
    rw [lintegral_lintegral_swap hF.aemeasurable]
    refine lintegral_congr fun s => ?_
    by_cases hs : s ∈ S
    · simp only [Set.indicator_of_mem hs]
      have : ∫⁻ e, (Iio e).indicator φ s ∂(expMeasure r) = φ s * expMeasure r (Ioi s) := by
        rw [← lintegral_indicator_const measurableSet_Ioi]
        refine lintegral_congr fun e => ?_
        by_cases he : s < e
        · rw [Set.indicator_of_mem (show s ∈ Iio e from he),
            Set.indicator_of_mem (show e ∈ Ioi s from he)]
        · rw [Set.indicator_of_notMem (show s ∉ Iio e from he),
            Set.indicator_of_notMem (show e ∉ Ioi s from he)]
      rw [this, expMeasure_Ioi hr (hS0 hs)]
    · simp only [Set.indicator_of_notMem hs, lintegral_zero]
  have hE : expMeasure r = volume.withDensity (exponentialPDF r) := rfl
  have hpm : Measurable (exponentialPDF r) := (measurable_exponentialPDFReal r).ennreal_ofReal
  rw [hswap, hE, lintegral_withDensity_eq_lintegral_mul _ hpm (hφ.indicator hS),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_indicator hS]
  refine lintegral_congr fun s => ?_
  by_cases hs : s ∈ S
  · simp only [Set.indicator_of_mem hs, Pi.mul_apply, exponentialPDF_eq, if_pos (show (0:ℝ) ≤ s from hS0 hs)]
    rw [ENNReal.ofReal_mul hr.le]
    ring
  · simp [Set.indicator_of_notMem hs]

/-- ASTA kernel: `E φ(e) = r E ∫_0^e φ`. -/
theorem exp_asta_core {r : ℝ} (hr : 0 < r) (φ : ℝ → ENNReal) (hφ : Measurable φ) :
    ∫⁻ e, φ e ∂(expMeasure r) =
      ENNReal.ofReal r * ∫⁻ e, (∫⁻ s in Ico 0 e, φ s) ∂(expMeasure r) := by
  have h := exp_weighted_set hr φ hφ measurableSet_Ici subset_rfl
  have h1 : ∫⁻ e, φ e ∂(expMeasure r) = ∫⁻ e, (Ici 0).indicator φ e ∂(expMeasure r) := by
    refine lintegral_congr_ae ?_
    filter_upwards [CM4W.expMeasure_ae_pos hr] with e he
    rw [indicator_of_mem (show e ∈ Ici (0:ℝ) from he.le)]
  have h2 : ∀ e : ℝ, ∫⁻ s in Ici 0, (Iio e).indicator φ s = ∫⁻ s in Ico 0 e, φ s := by
    intro e
    rw [← lintegral_indicator measurableSet_Ici, ← lintegral_indicator measurableSet_Ico,
      indicator_indicator, Ici_inter_Iio]
  rw [h1, ← h]
  simp only [h2]

/-- Translation of a set lintegral. -/
theorem lintegral_Ico_shift (h : ℝ → ENNReal) (a e : ℝ) :
    ∫⁻ s in Ico a (a + e), h s = ∫⁻ u in Ico 0 e, h (a + u) := by
  rw [← lintegral_indicator measurableSet_Ico, ← lintegral_indicator measurableSet_Ico,
    ← lintegral_add_left_eq_self ((Ico a (a + e)).indicator h) a]
  refine lintegral_congr fun u => ?_
  by_cases hu : u ∈ Ico 0 e
  · have : a + u ∈ Ico a (a + e) := ⟨by linarith [hu.1], by linarith [hu.2]⟩
    rw [indicator_of_mem this, indicator_of_mem hu]
  · have : a + u ∉ Ico a (a + e) := fun h' => hu ⟨by linarith [h'.1], by linarith [h'.2]⟩
    rw [indicator_of_notMem this, indicator_of_notMem hu]

end CM4C3

namespace CM4S1
open CoffmanMitrani MeasureTheory ProbabilityTheory Set CM4T CM4M CM4W

variable {M : ℕ}

theorem measurable_workAm' {α : Type*} [MeasurableSpace α] (A : Job M → Prop) {f : α → Omega M}
    (hf : Measurable f) {s t : α → ℝ} (hs : Measurable s) (ht : Measurable t) :
    Measurable (fun a => workAm (f a) A (s a) (t a)) := by
  refine (Measurable.ennreal_tsum (fun j => ?_)).ennreal_toReal
  refine ENNReal.measurable_ofReal.comp ?_
  have haj : Measurable (fun a => arrival (f a) j) := (measurable_arrival j).comp hf
  have hsj : Measurable (fun a => serviceReq (f a) j) := (measurable_serviceReq j).comp hf
  by_cases hA : A j
  · have hm : MeasurableSet {a : α | s a ≤ arrival (f a) j ∧ arrival (f a) j < t a} :=
      (measurableSet_le hs haj).inter (measurableSet_lt haj ht)
    have : (fun a => Set.indicator {j' : Job M | A j' ∧ s a ≤ arrival (f a) j' ∧
        arrival (f a) j' < t a} (serviceReq (f a)) j) =
        Set.indicator {a | s a ≤ arrival (f a) j ∧ arrival (f a) j < t a}
        (fun a => serviceReq (f a) j) := by
      funext a; simp only [Set.indicator, mem_setOf_eq, hA, true_and]
    rw [this]; exact hsj.indicator hm
  · have : (fun a => Set.indicator {j' : Job M | A j' ∧ s a ≤ arrival (f a) j' ∧
        arrival (f a) j' < t a} (serviceReq (f a)) j) = fun _ => 0 := by
      funext a; exact indicator_of_notMem (fun h => hA h.1) _
    rw [this]; exact measurable_const

theorem measurable_bqm' {α : Type*} [MeasurableSpace α] (A : Job M → Prop) {f : α → Omega M}
    (hf : Measurable f) {t : α → ℝ} (ht : Measurable t) (q : Job M) :
    Measurable (fun a => bqm (f a) A (t a) q) := by
  have haq : Measurable (fun a => arrival (f a) q) := (measurable_arrival q).comp hf
  have hm : MeasurableSet {a : α | A q ∧ 0 ≤ arrival (f a) q ∧ arrival (f a) q < t a} := by
    by_cases hA : A q
    · simp only [hA, true_and]
      exact (measurableSet_le measurable_const haq).inter (measurableSet_lt haq ht)
    · simp only [hA, false_and, setOf_false, MeasurableSet.empty]
  unfold bqm
  exact Measurable.ite hm (measurable_const.max ((measurable_workAm' A hf haq ht).sub
    (ht.sub haq))) measurable_const

/-- Jointly measurable backlog (any measurable parametrisation). -/
theorem measurable_backlogM' {α : Type*} [MeasurableSpace α] (A : Job M → Prop)
    {f : α → Omega M} (hf : Measurable f) {t : α → ℝ} (ht : Measurable t) :
    Measurable (fun a => backlogM (f a) A (t a)) :=
  Measurable.iSup (fun q => measurable_bqm' A hf ht q)

theorem arrival_mono_idx {ω : Omega M} (hpos : ∀ j : Job M, 0 ≤ ω.1 j) (c : Fin M) {n m : ℕ}
    (h : n ≤ m) : arrival ω (c, n) ≤ arrival ω (c, m) :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun k _ _ => hpos (c, k))

/-- Before `T_{c,n}` the backlog does not see class-`c` jobs of index `≥ n`. -/
theorem backlogA_trunc_eq {ω : Omega M} (hpos : ∀ j : Job M, 0 ≤ ω.1 j) (A : Job M → Prop)
    (c : Fin M) (n : ℕ) {s : ℝ} (hs : s ≤ arrival ω (c, n)) :
    backlogA ω A s = backlogA ω (trunc A c n) s := by
  refine backlogA_eq_of ω (fun q hq => hq.1) (fun q hA hn => ?_)
  obtain ⟨q1, q2⟩ := q
  have hq1 : q1 = c := by
    by_contra h; exact hn ⟨hA, fun h' => absurd h' h⟩
  have hq2 : n ≤ q2 := by
    by_contra h; exact hn ⟨hA, fun _ => by simp only at *; omega⟩
  subst hq1
  exact hs.trans (arrival_mono_idx hpos q1 hq2)

/-- **S1 (ASTA, class `c`).** `E ψ(V(T_n)) = λ_c E ∫_{T_{n-1}}^{T_n} ψ(V(s)) ds`
(`T_{n-1} = T_n - e_{c,n}`, `T_{-1} = 0`), for any measurable `ψ ≥ 0` and job set `A`. -/
theorem asta (D : Data) (A : Job D.M → Prop) (c : Fin D.M) (n : ℕ) (ψ : ℝ → ENNReal)
    (hψ : Measurable ψ) :
    ∫⁻ ω, ψ (backlogA ω A (arrival ω (c, n))) ∂D.P =
      ENNReal.ofReal (D.lam c) * ∫⁻ ω, (∫⁻ s in Ico (arrival ω (c, n) - ω.1 (c, n))
        (arrival ω (c, n)), ψ (backlogA ω A s)) ∂D.P := by
  haveI := P_isProb D
  have hr : 0 < D.lam c := D.lam_pos c
  haveI : IsProbabilityMeasure (expMeasure (D.lam c)) := isProbabilityMeasure_expMeasure hr
  haveI : IsProbabilityMeasure (expMeasure (D.lam (c, n).1)) := isProbabilityMeasure_expMeasure hr
  have hgood := CM4G.ae_good D
  have hT : Measurable (fun ω : Omega D.M => arrival ω (c, n)) := measurable_arrival (c, n)
  have hTp : Measurable (fun ω : Omega D.M => arrival ω (c, n) - ω.1 (c, n)) :=
    hT.sub ((measurable_pi_apply (c, n)).comp measurable_fst)
  have hres : ∀ F : Omega D.M → ENNReal, Measurable F →
      ∫⁻ ω, F ω ∂D.P = ∫⁻ ω, ∫⁻ e, F (upd ω c n e) ∂(expMeasure (D.lam c)) ∂D.P := by
    intro F hF
    have hmp := P_resampleA D (c, n)
    rw [← hmp.lintegral_comp hF]
    exact lintegral_prod_symm _ (hF.comp hmp.measurable).aemeasurable
  have hF1 : Measurable (fun ω : Omega D.M => ψ (backlogM ω (trunc A c n) (arrival ω (c, n)))) :=
    hψ.comp (measurable_backlogM' _ measurable_id hT)
  have hL : ∫⁻ ω, ψ (backlogA ω A (arrival ω (c, n))) ∂D.P =
      ∫⁻ ω, ψ (backlogM ω (trunc A c n) (arrival ω (c, n))) ∂D.P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hgood] with ω hω
    rw [backlogM_eq hω.1, ← backlogA_trunc_eq hω.2 A c n le_rfl]
  have hJ : Measurable (fun p : Omega D.M × ℝ => (Ico (arrival p.1 (c, n) - p.1.1 (c, n))
      (arrival p.1 (c, n))).indicator (fun s => ψ (backlogM p.1 (trunc A c n) s)) p.2) := by
    have hset : MeasurableSet {p : Omega D.M × ℝ | arrival p.1 (c, n) - p.1.1 (c, n) ≤ p.2 ∧
        p.2 < arrival p.1 (c, n)} :=
      (measurableSet_le (hTp.comp measurable_fst) measurable_snd).inter
        (measurableSet_lt measurable_snd (hT.comp measurable_fst))
    have hf : Measurable (fun p : Omega D.M × ℝ => ψ (backlogM p.1 (trunc A c n) p.2)) :=
      hψ.comp (measurable_backlogM' _ measurable_fst measurable_snd)
    have heq : (fun p : Omega D.M × ℝ => (Ico (arrival p.1 (c, n) - p.1.1 (c, n))
        (arrival p.1 (c, n))).indicator (fun s => ψ (backlogM p.1 (trunc A c n) s)) p.2) =
        {p : Omega D.M × ℝ | arrival p.1 (c, n) - p.1.1 (c, n) ≤ p.2 ∧
          p.2 < arrival p.1 (c, n)}.indicator (fun p => ψ (backlogM p.1 (trunc A c n) p.2)) := by
      funext p; simp only [Set.indicator, mem_setOf_eq, mem_Ico]
    rw [heq]; exact hf.indicator hset
  have hG1 : Measurable (fun ω : Omega D.M => ∫⁻ s, (Ico (arrival ω (c, n) - ω.1 (c, n))
      (arrival ω (c, n))).indicator (fun s => ψ (backlogM ω (trunc A c n) s)) s) :=
    hJ.lintegral_prod_right'
  have hR : ∫⁻ ω, (∫⁻ s in Ico (arrival ω (c, n) - ω.1 (c, n)) (arrival ω (c, n)),
        ψ (backlogA ω A s)) ∂D.P =
      ∫⁻ ω, (∫⁻ s, (Ico (arrival ω (c, n) - ω.1 (c, n)) (arrival ω (c, n))).indicator
        (fun s => ψ (backlogM ω (trunc A c n) s)) s) ∂D.P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hgood] with ω hω
    rw [← lintegral_indicator measurableSet_Ico]
    refine lintegral_congr fun s => ?_
    by_cases hs : s ∈ Ico (arrival ω (c, n) - ω.1 (c, n)) (arrival ω (c, n))
    · rw [indicator_of_mem hs, indicator_of_mem hs, backlogM_eq hω.1,
        ← backlogA_trunc_eq hω.2 A c n hs.2.le]
    · rw [indicator_of_notMem hs, indicator_of_notMem hs]
  rw [hL, hR, hres _ hF1, hres _ hG1, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr_ae ?_
  filter_upwards [hgood] with ω hω
  have hG := hω.1
  have hTa : ∀ e : ℝ, arrival (upd ω c n e) (c, n) = arrival ω (c, n) - ω.1 (c, n) + e := by
    intro e
    rw [arrival_upd, if_pos (show (c, n).1 = c ∧ n ≤ (c, n).2 from ⟨rfl, le_rfl⟩)]
    ring
  have hTpa : ∀ e : ℝ, arrival (upd ω c n e) (c, n) - (upd ω c n e).1 (c, n) =
      arrival ω (c, n) - ω.1 (c, n) := by
    intro e
    rw [hTa]
    simp only [upd, Function.update_self]
    ring
  have hBM : ∀ e s : ℝ, backlogM (upd ω c n e) (trunc A c n) s = backlogM ω (trunc A c n) s := by
    intro e s
    rw [backlogM_eq (FinGood_upd (i := c) (m := n) (x := e) hG),
      backlogA_trunc_upd ω e A (le_refl n), backlogM_eq hG]
  set a := arrival ω (c, n) - ω.1 (c, n) with ha
  have hφ : Measurable (fun u : ℝ => ψ (backlogM ω (trunc A c n) (a + u))) :=
    hψ.comp (measurable_backlogM' _ measurable_const (measurable_id.const_add a))
  have h1 : ∀ e : ℝ, ψ (backlogM (upd ω c n e) (trunc A c n) (arrival (upd ω c n e) (c, n))) =
      ψ (backlogM ω (trunc A c n) (a + e)) := by
    intro e; rw [hBM, hTa]
  have h2 : ∀ e : ℝ, ∫⁻ s, (Ico (arrival (upd ω c n e) (c, n) - (upd ω c n e).1 (c, n))
      (arrival (upd ω c n e) (c, n))).indicator
        (fun s => ψ (backlogM (upd ω c n e) (trunc A c n) s)) s =
      ∫⁻ u in Ico 0 e, ψ (backlogM ω (trunc A c n) (a + u)) := by
    intro e
    rw [hTpa, hTa, lintegral_indicator measurableSet_Ico]
    simp only [hBM]
    exact CM4C3.lintegral_Ico_shift _ a e
  simp only [h1, h2]
  exact CM4C3.exp_asta_core hr _ hφ

end CM4S1

/-! S2 foundations (relay 15): Lindley dynamics of `backlogA` and the calculus identity. -/
namespace CM4S2
open CoffmanMitrani MeasureTheory Set CM4T CM4M

variable {M : ℕ}

theorem workA_add {ω : Omega M} (hG : FinGood ω) (A : Job M → Prop) {u t s : ℝ} (hut : u ≤ t)
    (hts : t ≤ s) : workA ω A u s = workA ω A u t + workA ω A t s := by
  have hset : {j : Job M | A j ∧ u ≤ arrival ω j ∧ arrival ω j < s} =
      {j : Job M | A j ∧ u ≤ arrival ω j ∧ arrival ω j < t} ∪
        {j : Job M | A j ∧ t ≤ arrival ω j ∧ arrival ω j < s} := by
    ext j
    simp only [mem_union, mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2, h3⟩
      rcases lt_or_ge (arrival ω j) t with h | h
      · exact Or.inl ⟨h1, h2, h⟩
      · exact Or.inr ⟨h1, h, h3⟩
    · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
      · exact ⟨h1, h2, by linarith⟩
      · exact ⟨h1, by linarith, h3⟩
  have hdisj : Disjoint {j : Job M | A j ∧ u ≤ arrival ω j ∧ arrival ω j < t}
      {j : Job M | A j ∧ t ≤ arrival ω j ∧ arrival ω j < s} :=
    Set.disjoint_left.2 fun j h h' => by
      simp only [mem_setOf_eq] at h h'
      linarith [h.2.2, h'.2.1]
  unfold workA
  rw [hset, indicator_union_of_disjoint hdisj]
  exact (workA_summable hG A u t).tsum_add (workA_summable hG A t s)

theorem bdd_img {ω : Omega M} (hG : FinGood ω) (A : Job M → Prop) (s : ℝ) :
    BddAbove ((fun u => workA ω A u s - (s - u)) '' Icc 0 s) := ⟨workA ω A 0 s, by
  rintro _ ⟨u, hu, rfl⟩
  have := workA_mono hG (fun q h => h) hu.1 (le_refl s) (A := A)
  dsimp only; linarith [hu.2]⟩

theorem le_backlog {ω : Omega M} (hG : FinGood ω) (A : Job M → Prop) {u s : ℝ} (hu : u ∈ Icc 0 s) :
    workA ω A u s - (s - u) ≤ backlogA ω A s :=
  le_max_of_le_right (le_csSup (bdd_img hG A s) ⟨u, hu, rfl⟩)

/-- Lindley lower bound: `V(s) ≥ V(t) + W[t,s) - (s - t)`. -/
theorem backlog_ge {ω : Omega M} (hG : FinGood ω) (A : Job M → Prop) {t s : ℝ} (ht : 0 ≤ t)
    (hts : t ≤ s) : backlogA ω A t + (workA ω A t s - (s - t)) ≤ backlogA ω A s := by
  have h0 : workA ω A t s - (s - t) ≤ backlogA ω A s := le_backlog hG A ⟨ht, hts⟩
  have h1 : sSup ((fun u => workA ω A u t - (t - u)) '' Icc 0 t) ≤
      backlogA ω A s - (workA ω A t s - (s - t)) := by
    refine csSup_le ((nonempty_Icc.2 ht).image _) ?_
    rintro _ ⟨u, hu, rfl⟩
    have := le_backlog hG A (s := s) ⟨hu.1, hu.2.trans hts⟩
    rw [workA_add hG A hu.2 hts] at this
    dsimp only; linarith
  have hV : backlogA ω A t = max 0 (sSup ((fun u => workA ω A u t - (t - u)) '' Icc 0 t)) := rfl
  rw [hV]
  rcases le_total 0 (sSup ((fun u => workA ω A u t - (t - u)) '' Icc 0 t)) with h | h
  · rw [max_eq_right h]; linarith
  · rw [max_eq_left h]; linarith

/-- Lindley upper bound when no `A`-job arrives in `(t, s)`. -/
theorem backlog_le {ω : Omega M} (hG : FinGood ω) (A : Job M → Prop) {t s : ℝ} (ht : 0 ≤ t)
    (hts : t ≤ s) (hno : ∀ q, A q → arrival ω q < s → arrival ω q ≤ t) :
    backlogA ω A s ≤ max 0 (backlogA ω A t + (workA ω A t s - (s - t))) := by
  refine max_le (le_max_left _ _) ?_
  refine csSup_le ((nonempty_Icc.2 (ht.trans hts)).image _) ?_
  rintro _ ⟨u, hu, rfl⟩
  dsimp only
  rcases le_or_gt u t with hut | htu
  · have h1 : workA ω A u t - (t - u) ≤ backlogA ω A t := le_backlog hG A ⟨hu.1, hut⟩
    rw [workA_add hG A hut hts]
    exact le_max_of_le_right (by linarith)
  · have hw : workA ω A u s = 0 := by
      unfold workA
      refine (tsum_congr (fun q => indicator_of_notMem (fun hq => ?_) _)).trans tsum_zero
      obtain ⟨h1, h2, h3⟩ := hq
      linarith [hno q h1 h3]
    rw [hw]
    exact le_max_of_le_left (by linarith [hu.2])

/-- Exact Lindley step when no `A`-job arrives in `(t, s)`. -/
theorem backlog_step {ω : Omega M} (hG : FinGood ω) (A : Job M → Prop) {t s : ℝ} (ht : 0 ≤ t)
    (hts : t ≤ s) (hno : ∀ q, A q → arrival ω q < s → arrival ω q ≤ t) :
    backlogA ω A s = max 0 (backlogA ω A t + (workA ω A t s - (s - t))) :=
  le_antisymm (backlog_le hG A ht hts hno)
    (max_le (backlogA_nonneg ω A s) (backlog_ge hG A ht hts))

/-- **Calculus identity** behind S2: `max(0,y-h)^{p+1} + (p+1) ∫_0^h max(0,y-s)^p ds = y^{p+1}`. -/
theorem calc_id {y h : ℝ} (hy : 0 ≤ y) (hh : 0 ≤ h) {p : ℕ} (hp : 1 ≤ p) :
    (max 0 (y - h)) ^ (p + 1) + (p + 1) * ∫ s in (0:ℝ)..h, (max 0 (y - s)) ^ p = y ^ (p + 1) := by
  have hp1 : (p : ℝ) + 1 ≠ 0 := by positivity
  have key : ∀ b : ℝ, 0 ≤ b → b ≤ y → ∫ s in (0:ℝ)..b, (max 0 (y - s)) ^ p =
      (y ^ (p + 1) - (y - b) ^ (p + 1)) / (p + 1) := by
    intro b hb hby
    have : ∫ s in (0:ℝ)..b, (max 0 (y - s)) ^ p = ∫ s in (0:ℝ)..b, (y - s) ^ p := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le hb] at hs
      rw [max_eq_right (by linarith [hs.2])]
    rw [this, intervalIntegral.integral_comp_sub_left (fun x => x ^ p), integral_pow, sub_zero]
  have hcont : Continuous (fun s : ℝ => (max 0 (y - s)) ^ p) :=
    (continuous_const.max (continuous_const.sub continuous_id)).pow p
  rcases le_total h y with hhy | hyh
  · rw [key h hh hhy, max_eq_right (by linarith)]
    have : ((p : ℝ) + 1) * ((y ^ (p + 1) - (y - h) ^ (p + 1)) / (p + 1)) =
        y ^ (p + 1) - (y - h) ^ (p + 1) := by field_simp
    linarith
  · have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable (μ := MeasureTheory.volume) 0 y)
      (hcont.intervalIntegrable (μ := MeasureTheory.volume) y h)
    have hz : ∫ s in y..h, (max 0 (y - s)) ^ p = 0 := by
      have : ∫ s in y..h, (max 0 (y - s)) ^ p = ∫ s in y..h, (0:ℝ) := by
        refine intervalIntegral.integral_congr fun s hs => ?_
        rw [uIcc_of_le hyh] at hs
        show (max 0 (y - s)) ^ p = 0
        rw [max_eq_left (by linarith [hs.1]), zero_pow (by omega)]
      rw [this, intervalIntegral.integral_zero]
    rw [← hsplit, hz, add_zero, key y hy le_rfl, sub_self, zero_pow (by omega), sub_zero,
      max_eq_left (by linarith), zero_pow (by omega), zero_add]
    field_simp

theorem backlog_zero {ω : Omega M} (A : Job M → Prop) {s : ℝ} (hs : 0 ≤ s)
    (hno : ∀ q, A q → ¬ arrival ω q < s) : backlogA ω A s = 0 := by
  refine le_antisymm (max_le le_rfl ?_) (backlogA_nonneg ω A s)
  refine csSup_le ((nonempty_Icc.2 hs).image _) ?_
  rintro _ ⟨u, hu, rfl⟩
  have hw : workA ω A u s = 0 := by
    unfold workA
    exact (tsum_congr (fun q => indicator_of_notMem (fun hq => hno q hq.1 hq.2.2) _)).trans
      tsum_zero
  dsimp only
  rw [hw]
  linarith [hu.2]

theorem ii_of_eqOn {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hg : Continuous g)
    (h : ∀ s ∈ Ioc a b, g s = f s) : IntervalIntegrable f volume a b :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
    (((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1
      (hg.intervalIntegrable a b)).congr_fun h measurableSet_Ioc)

/-- **S2 pathwise identity** (induction over the arrivals before `t`):
`V(t)^{p+1} + (p+1) ∫_0^t V^p = Σ_{A-jobs q, a_q < t} [(V(a_q)+X_q)^{p+1} - V(a_q)^{p+1}]`,
for distinct `A`-arrival times and nonnegative interarrivals. -/
theorem pathwise {ω : Omega M} (hG : FinGood ω) (hpos : ∀ j : Job M, 0 ≤ ω.1 j)
    (A : Job M → Prop)
    (hdist : ∀ q q', A q → A q' → arrival ω q = arrival ω q' → q = q') {p : ℕ} (hp : 1 ≤ p) :
    ∀ (n : ℕ) (t : ℝ) (F : Finset (Job M)), 0 ≤ t → (∀ q, q ∈ F ↔ A q ∧ arrival ω q < t) →
      F.card = n →
      IntervalIntegrable (fun s => (backlogA ω A s) ^ p) volume 0 t ∧
      (backlogA ω A t) ^ (p + 1) + (p + 1) * ∫ s in (0:ℝ)..t, (backlogA ω A s) ^ p =
        ∑ q ∈ F, ((backlogA ω A (arrival ω q) + serviceReq ω q) ^ (p + 1) -
          (backlogA ω A (arrival ω q)) ^ (p + 1)) := by
  intro n
  induction n with
  | zero =>
    intro t F ht hF hc
    have hF0 : F = ∅ := Finset.card_eq_zero.1 hc
    have hV0 : ∀ s, 0 ≤ s → s ≤ t → backlogA ω A s = 0 := fun s hs0 hst =>
      backlog_zero A hs0 (fun q hA hq => by
        have := (hF q).2 ⟨hA, lt_of_lt_of_le hq hst⟩
        rw [hF0] at this
        exact Finset.notMem_empty q this)
    have hcongr : EqOn (fun s => (backlogA ω A s) ^ p) (fun _ => (0:ℝ)) (uIcc 0 t) := by
      intro s hs
      rw [uIcc_of_le ht] at hs
      show (backlogA ω A s) ^ p = 0
      rw [hV0 s hs.1 hs.2, zero_pow (by omega)]
    have hmem : ∀ s ∈ Ioc (0:ℝ) t, s ∈ uIcc 0 t := fun s hs => by
      rw [uIcc_of_le ht]; exact Ioc_subset_Icc_self hs
    refine ⟨ii_of_eqOn ht continuous_const (fun s hs => (hcongr (hmem s hs)).symm), ?_⟩
    rw [hF0, Finset.sum_empty, hV0 t ht le_rfl, intervalIntegral.integral_congr hcongr,
      intervalIntegral.integral_zero]
    simp
  | succ n ih =>
    intro t F ht hF hc
    have hne : F.Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨qs, hqs, hmax⟩ := Finset.exists_max_image F (fun q => arrival ω q) hne
    have hqsF := (hF qs).1 hqs
    have hτt : arrival ω qs < t := hqsF.2
    have hτ0 : 0 ≤ arrival ω qs :=
      Finset.sum_nonneg (fun k _ => hpos (qs.1, k))
    have hF' : ∀ q, q ∈ F.erase qs ↔ A q ∧ arrival ω q < arrival ω qs := by
      intro q
      rw [Finset.mem_erase]
      constructor
      · rintro ⟨hq, hqF⟩
        have h1 := (hF q).1 hqF
        refine ⟨h1.1, lt_of_le_of_ne (hmax q hqF) (fun he => hq (hdist q qs h1.1 hqsF.1 he))⟩
      · rintro ⟨hA, hlt⟩
        exact ⟨fun he => by rw [he] at hlt; exact lt_irrefl _ hlt,
          (hF q).2 ⟨hA, hlt.trans hτt⟩⟩
    have hcard : (F.erase qs).card = n := by
      rw [Finset.card_erase_of_mem hqs, hc]; rfl
    obtain ⟨hI, hEq⟩ := ih (arrival ω qs) (F.erase qs) hτ0 hF' hcard
    have hno : ∀ q, A q → arrival ω q < t → arrival ω q ≤ arrival ω qs :=
      fun q hA h => hmax q ((hF q).2 ⟨hA, h⟩)
    have hW : ∀ s, arrival ω qs < s → s ≤ t → workA ω A (arrival ω qs) s = serviceReq ω qs := by
      intro s h1 h2
      unfold workA
      rw [tsum_eq_single qs]
      · exact indicator_of_mem (show qs ∈ {j : Job M | A j ∧ arrival ω qs ≤ arrival ω j ∧
          arrival ω j < s} from ⟨hqsF.1, le_rfl, h1⟩) _
      · intro q hq
        refine indicator_of_notMem (fun hm => hq ?_) _
        obtain ⟨hA, ha1, ha2⟩ := hm
        exact hdist q qs hA hqsF.1 (le_antisymm (hno q hA (lt_of_lt_of_le ha2 h2)) ha1)
    have hVs : ∀ s ∈ Ioc (arrival ω qs) t, backlogA ω A s =
        max 0 (backlogA ω A (arrival ω qs) + serviceReq ω qs - (s - arrival ω qs)) := by
      intro s hs
      rw [backlog_step hG A hτ0 hs.1.le (fun q hA h => hno q hA (lt_of_lt_of_le h hs.2)),
        hW s hs.1 hs.2]
      congr 1
      ring
    have hcont2 : Continuous (fun s : ℝ => (max 0 (backlogA ω A (arrival ω qs) + serviceReq ω qs -
        (s - arrival ω qs))) ^ p) :=
      (continuous_const.max (continuous_const.sub (continuous_id.sub continuous_const))).pow p
    have hI2 : IntervalIntegrable (fun s => (backlogA ω A s) ^ p) volume (arrival ω qs) t :=
      ii_of_eqOn hτt.le hcont2 (fun s hs => by rw [hVs s hs])
    have hint2 : ∫ s in (arrival ω qs)..t, (backlogA ω A s) ^ p =
        ∫ u in (0:ℝ)..(t - arrival ω qs),
          (max 0 (backlogA ω A (arrival ω qs) + serviceReq ω qs - u)) ^ p := by
      rw [intervalIntegral.integral_congr_ae (g := fun s => (max 0 (backlogA ω A (arrival ω qs) +
        serviceReq ω qs - (s - arrival ω qs))) ^ p) (Filter.Eventually.of_forall fun s hs => by
          rw [uIoc_of_le hτt.le] at hs
          rw [hVs s hs]),
        intervalIntegral.integral_comp_sub_right
          (fun u => (max 0 (backlogA ω A (arrival ω qs) + serviceReq ω qs - u)) ^ p), sub_self]
    have hy : 0 ≤ backlogA ω A (arrival ω qs) + serviceReq ω qs :=
      add_nonneg (backlogA_nonneg ω A _) (hG.1 qs)
    have hcalc := calc_id hy (show 0 ≤ t - arrival ω qs by linarith) hp
    have hVt := hVs t ⟨hτt, le_rfl⟩
    refine ⟨hI.trans hI2, ?_⟩
    rw [← Finset.sum_erase_add F _ hqs, ← hEq,
      ← intervalIntegral.integral_add_adjacent_intervals hI hI2, hint2, hVt, mul_add]
    linarith [hcalc]

/-- (a) for S2: almost surely all arrival times are distinct. -/
theorem ae_arrival_inj (D : Data) :
    ∀ᵐ ω ∂D.P, ∀ q q' : Job D.M, arrival ω q = arrival ω q' → q = q' := by
  have hpos := CM4G.ae_interarrival_pos D
  have hpair : ∀ q q' : Job D.M, ∀ᵐ ω ∂D.P, arrival ω q = arrival ω q' → q = q' := by
    intro q q'
    by_cases hqq : q = q'
    · exact Filter.Eventually.of_forall fun _ _ => hqq
    obtain ⟨i, m⟩ := q
    obtain ⟨i', m'⟩ := q'
    by_cases hi : i = i'
    · subst hi
      have hm : m ≠ m' := fun h => hqq (by rw [h])
      filter_upwards [hpos] with ω hω
      intro heq
      exfalso
      have hlt : ∀ a b : ℕ, a < b → arrival ω (i, a) < arrival ω (i, b) := by
        intro a b hab
        show ∑ k ∈ Finset.range (a + 1), ω.1 (i, k) < ∑ k ∈ Finset.range (b + 1), ω.1 (i, k)
        exact Finset.sum_lt_sum_of_subset (Finset.range_mono (by omega))
          (Finset.mem_range.2 (show b < b + 1 by omega))
          (fun h => by rw [Finset.mem_range] at h; omega) (hω (i, b))
          (fun k _ _ => (hω (i, k)).le)
      rcases lt_or_gt_of_ne hm with h | h
      · exact (hlt m m' h).ne heq
      · exact (hlt m' m h).ne heq.symm
    · have hnull := CM4W.P_eq_null D (i, 0)
        (fun ω => arrival ω (i', m') - (arrival ω (i, m) - ω.1 (i, 0)))
        ((measurable_arrival _).sub ((measurable_arrival _).sub
          ((measurable_pi_apply _).comp measurable_fst)))
        (fun ω x => by
          show arrival (upd ω i 0 x) (i', m') - (arrival (upd ω i 0 x) (i, m) -
              (upd ω i 0 x).1 (i, 0)) = arrival ω (i', m') - (arrival ω (i, m) - ω.1 (i, 0))
          rw [arrival_upd_of ω i 0 x (q := (i', m')) (fun h => absurd h (Ne.symm hi)),
            arrival_upd, if_pos (show (i, m).1 = i ∧ 0 ≤ (i, m).2 from ⟨rfl, Nat.zero_le _⟩)]
          simp only [upd, Function.update_self]
          ring)
      rw [ae_iff]
      refine measure_mono_null (fun ω hω => ?_) hnull
      have hω' : arrival ω (i, m) = arrival ω (i', m') := (_root_.not_imp.1 hω).1
      show ω.1 (i, 0) = arrival ω (i', m') - (arrival ω (i, m) - ω.1 (i, 0))
      linarith
  exact ae_all_iff.2 fun q => ae_all_iff.2 (hpair q)

end CM4S2

namespace CM4S3
open CoffmanMitrani MeasureTheory ProbabilityTheory Set CM4T CM4M CM4W CM4S1

/-- **S3b core (ASTA with a deadline).** For a deadline `ν` that does not depend on the
interarrival `e_{c,n}`: `E[ψ(V(T_n)); T_n < ν] = λ_c E ∫_{T_{n-1}}^{min(T_n, ν)} ψ(V)`. -/
theorem asta_dl (D : Data) (A : Job D.M → Prop) (c : Fin D.M) (n : ℕ) (ψ : ℝ → ENNReal)
    (hψ : Measurable ψ) (ν : Omega D.M → ℝ) (hν : Measurable ν)
    (hνinv : ∀ (ω : Omega D.M) (x : ℝ), ν (upd ω c n x) = ν ω) :
    ∫⁻ ω, {ω | arrival ω (c, n) < ν ω}.indicator
        (fun ω => ψ (backlogA ω A (arrival ω (c, n)))) ω ∂D.P =
      ENNReal.ofReal (D.lam c) * ∫⁻ ω, (∫⁻ s in Ico (arrival ω (c, n) - ω.1 (c, n))
        (min (arrival ω (c, n)) (ν ω)), ψ (backlogA ω A s)) ∂D.P := by
  haveI := P_isProb D
  have hr : 0 < D.lam c := D.lam_pos c
  haveI : IsProbabilityMeasure (expMeasure (D.lam c)) := isProbabilityMeasure_expMeasure hr
  have hgood := CM4G.ae_good D
  have hT : Measurable (fun ω : Omega D.M => arrival ω (c, n)) := measurable_arrival (c, n)
  have hTp : Measurable (fun ω : Omega D.M => arrival ω (c, n) - ω.1 (c, n)) :=
    hT.sub ((measurable_pi_apply (c, n)).comp measurable_fst)
  have hres : ∀ F : Omega D.M → ENNReal, Measurable F →
      ∫⁻ ω, F ω ∂D.P = ∫⁻ ω, ∫⁻ e, F (upd ω c n e) ∂(expMeasure (D.lam c)) ∂D.P := by
    intro F hF
    have hmp := P_resampleA D (c, n)
    rw [← hmp.lintegral_comp hF]
    exact lintegral_prod_symm _ (hF.comp hmp.measurable).aemeasurable
  have hF1 : Measurable (fun ω : Omega D.M => {ω : Omega D.M | arrival ω (c, n) < ν ω}.indicator
      (fun ω => ψ (backlogM ω (trunc A c n) (arrival ω (c, n)))) ω) :=
    (hψ.comp (measurable_backlogM' _ measurable_id hT)).indicator (measurableSet_lt hT hν)
  have hL : ∫⁻ ω, {ω | arrival ω (c, n) < ν ω}.indicator
        (fun ω => ψ (backlogA ω A (arrival ω (c, n)))) ω ∂D.P =
      ∫⁻ ω, {ω : Omega D.M | arrival ω (c, n) < ν ω}.indicator
        (fun ω => ψ (backlogM ω (trunc A c n) (arrival ω (c, n)))) ω ∂D.P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hgood] with ω hω
    simp only [Set.indicator_apply, mem_setOf_eq]
    rw [backlogM_eq hω.1, ← backlogA_trunc_eq hω.2 A c n le_rfl]
  have hJ : Measurable (fun p : Omega D.M × ℝ => (Ico (arrival p.1 (c, n) - p.1.1 (c, n))
      (min (arrival p.1 (c, n)) (ν p.1))).indicator
        (fun s => ψ (backlogM p.1 (trunc A c n) s)) p.2) := by
    have hset : MeasurableSet {p : Omega D.M × ℝ | arrival p.1 (c, n) - p.1.1 (c, n) ≤ p.2 ∧
        p.2 < min (arrival p.1 (c, n)) (ν p.1)} :=
      (measurableSet_le (hTp.comp measurable_fst) measurable_snd).inter
        (measurableSet_lt measurable_snd ((hT.min hν).comp measurable_fst))
    have hf : Measurable (fun p : Omega D.M × ℝ => ψ (backlogM p.1 (trunc A c n) p.2)) :=
      hψ.comp (measurable_backlogM' _ measurable_fst measurable_snd)
    have heq : (fun p : Omega D.M × ℝ => (Ico (arrival p.1 (c, n) - p.1.1 (c, n))
        (min (arrival p.1 (c, n)) (ν p.1))).indicator
          (fun s => ψ (backlogM p.1 (trunc A c n) s)) p.2) =
        {p : Omega D.M × ℝ | arrival p.1 (c, n) - p.1.1 (c, n) ≤ p.2 ∧
          p.2 < min (arrival p.1 (c, n)) (ν p.1)}.indicator
            (fun p => ψ (backlogM p.1 (trunc A c n) p.2)) := by
      funext p; simp only [Set.indicator, mem_setOf_eq, mem_Ico]
    rw [heq]; exact hf.indicator hset
  have hG1 : Measurable (fun ω : Omega D.M => ∫⁻ s, (Ico (arrival ω (c, n) - ω.1 (c, n))
      (min (arrival ω (c, n)) (ν ω))).indicator (fun s => ψ (backlogM ω (trunc A c n) s)) s) :=
    hJ.lintegral_prod_right'
  have hR : ∫⁻ ω, (∫⁻ s in Ico (arrival ω (c, n) - ω.1 (c, n)) (min (arrival ω (c, n)) (ν ω)),
        ψ (backlogA ω A s)) ∂D.P =
      ∫⁻ ω, (∫⁻ s, (Ico (arrival ω (c, n) - ω.1 (c, n)) (min (arrival ω (c, n)) (ν ω))).indicator
        (fun s => ψ (backlogM ω (trunc A c n) s)) s) ∂D.P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hgood] with ω hω
    rw [← lintegral_indicator measurableSet_Ico]
    refine lintegral_congr fun s => ?_
    by_cases hs : s ∈ Ico (arrival ω (c, n) - ω.1 (c, n)) (min (arrival ω (c, n)) (ν ω))
    · rw [indicator_of_mem hs, indicator_of_mem hs, backlogM_eq hω.1,
        ← backlogA_trunc_eq hω.2 A c n (hs.2.trans_le (min_le_left _ _)).le]
    · rw [indicator_of_notMem hs, indicator_of_notMem hs]
  rw [hL, hR, hres _ hF1, hres _ hG1, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr_ae ?_
  filter_upwards [hgood] with ω hω
  have hG := hω.1
  have hTa : ∀ e : ℝ, arrival (upd ω c n e) (c, n) = arrival ω (c, n) - ω.1 (c, n) + e := by
    intro e
    rw [arrival_upd, if_pos (show (c, n).1 = c ∧ n ≤ (c, n).2 from ⟨rfl, le_rfl⟩)]
    ring
  have hTpa : ∀ e : ℝ, arrival (upd ω c n e) (c, n) - (upd ω c n e).1 (c, n) =
      arrival ω (c, n) - ω.1 (c, n) := by
    intro e
    rw [hTa]
    simp only [upd, Function.update_self]
    ring
  have hBM : ∀ e s : ℝ, backlogM (upd ω c n e) (trunc A c n) s = backlogM ω (trunc A c n) s := by
    intro e s
    rw [backlogM_eq (FinGood_upd (i := c) (m := n) (x := e) hG),
      backlogA_trunc_upd ω e A (le_refl n), backlogM_eq hG]
  set a := arrival ω (c, n) - ω.1 (c, n) with ha
  have hφ : Measurable (fun u : ℝ => ψ (backlogM ω (trunc A c n) (a + u))) :=
    hψ.comp (measurable_backlogM' _ measurable_const (measurable_id.const_add a))
  have h1 : ∀ e : ℝ, 0 < e → {ω : Omega D.M | arrival ω (c, n) < ν ω}.indicator
      (fun ω => ψ (backlogM ω (trunc A c n) (arrival ω (c, n)))) (upd ω c n e) =
      (Ico 0 (ν ω - a)).indicator (fun u => ψ (backlogM ω (trunc A c n) (a + u))) e := by
    intro e he
    simp only [Set.indicator_apply, mem_setOf_eq, mem_Ico, hTa, hνinv, hBM]
    by_cases h : a + e < ν ω
    · rw [if_pos h, if_pos ⟨he.le, by linarith⟩]
    · rw [if_neg h, if_neg (fun h' => h (by linarith [h'.2]))]
  have h2 : ∀ e : ℝ, ∫⁻ s, (Ico (arrival (upd ω c n e) (c, n) - (upd ω c n e).1 (c, n))
      (min (arrival (upd ω c n e) (c, n)) (ν (upd ω c n e)))).indicator
        (fun s => ψ (backlogM (upd ω c n e) (trunc A c n) s)) s =
      ∫⁻ u in Ico 0 (ν ω - a), (Iio e).indicator
        (fun u => ψ (backlogM ω (trunc A c n) (a + u))) u := by
    intro e
    rw [hTpa, hTa, hνinv, lintegral_indicator measurableSet_Ico]
    simp only [hBM]
    have hmin : min (a + e) (ν ω) = a + min e (ν ω - a) := by
      rw [← min_add_add_left]; congr 1; ring
    have hset : Ico 0 (ν ω - a) ∩ Iio e = Ico 0 (min e (ν ω - a)) := by
      ext u; simp only [mem_inter_iff, mem_Ico, mem_Iio, lt_min_iff]; tauto
    rw [hmin, CM4C3.lintegral_Ico_shift, ← lintegral_indicator measurableSet_Ico,
      ← lintegral_indicator measurableSet_Ico, Set.indicator_indicator, hset]
  refine Eq.trans (lintegral_congr_ae (g := fun e => (Ico 0 (ν ω - a)).indicator
      (fun u => ψ (backlogM ω (trunc A c n) (a + u))) e) ?_) ?_
  · filter_upwards [expMeasure_ae_pos hr] with e he using h1 e he
  simp only [h2]
  exact (CM4C3.exp_weighted_set hr _ hφ measurableSet_Ico (fun u hu => hu.1)).symm

/-- The interarrival pieces `[T_{m-1}, min(T_m, ν))` tile `[0, ν)`. -/
theorem tsum_pieces (e : ℕ → ℝ) (he : ∀ k, 0 ≤ e k)
    (hunb : ∀ t, ∃ m, t ≤ ∑ k ∈ Finset.range (m + 1), e k) (ν : ℝ) (f : ℝ → ENNReal) :
    ∑' m, ∫⁻ s in Ico (∑ k ∈ Finset.range (m + 1), e k - e m)
        (min (∑ k ∈ Finset.range (m + 1), e k) ν), f s = ∫⁻ s in Ico 0 ν, f s := by
  set S : ℕ → ℝ := fun m => ∑ k ∈ Finset.range m, e k with hS
  have hmono : Monotone S := fun a b hab =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab) (fun k _ _ => he k)
  have hpc : ∀ m, Ico (∑ k ∈ Finset.range (m + 1), e k - e m)
      (min (∑ k ∈ Finset.range (m + 1), e k) ν) = Ico (S m) (S (m + 1)) ∩ Iio ν := by
    intro m
    simp only [hS, Finset.sum_range_succ, add_sub_cancel_right]
    ext s; simp only [mem_Ico, mem_inter_iff, mem_Iio, lt_min_iff]; tauto
  have hdisj : Pairwise (Function.onFun Disjoint fun m => Ico (S m) (S (m + 1)) ∩ Iio ν) := by
    intro m m' hmm'
    rw [Function.onFun, Set.disjoint_left]
    intro s hs hs'
    rcases lt_or_gt_of_ne hmm' with h | h
    · exact absurd (hs.1.2.trans_le (hmono (Nat.succ_le_of_lt h))) (not_lt.2 hs'.1.1)
    · exact absurd (hs'.1.2.trans_le (hmono (Nat.succ_le_of_lt h))) (not_lt.2 hs.1.1)
  have hU : (⋃ m, Ico (S m) (S (m + 1)) ∩ Iio ν) = Ico 0 ν := by
    ext s; simp only [mem_iUnion, mem_inter_iff, mem_Ico, mem_Iio]
    constructor
    · rintro ⟨m, ⟨h1, _⟩, h3⟩
      exact ⟨(Finset.sum_nonneg fun k _ => he k).trans h1, h3⟩
    · rintro ⟨h0, h3⟩
      have hex : ∃ m, s < S (m + 1) := by
        obtain ⟨m, hm⟩ := hunb (s + 1)
        exact ⟨m, by simp only [hS]; linarith⟩
      classical
      refine ⟨Nat.find hex, ⟨?_, Nat.find_spec hex⟩, h3⟩
      rcases Nat.eq_zero_or_pos (Nat.find hex) with hz | hp
      · rw [hz]; simpa [hS] using h0
      · obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hp).symm⟩
        have := Nat.find_min hex (show k < Nat.find hex by omega)
        rw [hk]; exact not_lt.1 this
  calc ∑' m, ∫⁻ s in Ico (∑ k ∈ Finset.range (m + 1), e k - e m)
        (min (∑ k ∈ Finset.range (m + 1), e k) ν), f s
      = ∑' m, ∫⁻ s in Ico (S m) (S (m + 1)) ∩ Iio ν, f s := by
        congr 1; funext m; rw [hpc m]
    _ = ∫⁻ s in ⋃ m, Ico (S m) (S (m + 1)) ∩ Iio ν, f s :=
        (lintegral_iUnion (fun m => measurableSet_Ico.inter measurableSet_Iio) hdisj f).symm
    _ = _ := by rw [hU]

/-- **S3b (class-`i` arrivals see time averages up to a deadline).** For a deadline `ν`
independent of the class-`i` interarrivals:
`E Σ_m ψ(V(T_{i,m})) 1{T_{i,m} < ν} = λ_i E ∫_0^ν ψ(V(s)) ds`. -/
theorem exists_arr_ge' {M : ℕ} {ω : Omega M} (hG : FinGood ω) (i : Fin M) (t : ℝ) :
    ∃ N, t ≤ ∑ k ∈ Finset.range (N + 1), ω.1 (i, k) := by
  by_contra hcon
  push_neg at hcon
  exact Set.infinite_of_injective_forall_mem (f := fun N : ℕ => ((i, N) : Job M))
    (fun a b hab => congrArg Prod.snd hab) (fun N => (hcon N : arrival ω (i, N) < t)) (hG.2 t)

theorem arr_wald (D : Data) (A : Job D.M → Prop) (i : Fin D.M) (ψ : ℝ → ENNReal)
    (hψ : Measurable ψ) (ν : Omega D.M → ℝ) (hν : Measurable ν)
    (hνinv : ∀ (m : ℕ) (ω : Omega D.M) (x : ℝ), ν (upd ω i m x) = ν ω) :
    ∫⁻ ω, ∑' m, {ω | arrival ω (i, m) < ν ω}.indicator
        (fun ω => ψ (backlogA ω A (arrival ω (i, m)))) ω ∂D.P =
      ENNReal.ofReal (D.lam i) * ∫⁻ ω, (∫⁻ s in Ico 0 (ν ω), ψ (backlogA ω A s)) ∂D.P := by
  have hgood := CM4G.ae_good D
  have hmeasm : ∀ m, AEMeasurable (fun ω => {ω : Omega D.M | arrival ω (i, m) < ν ω}.indicator
      (fun ω => ψ (backlogA ω A (arrival ω (i, m)))) ω) D.P := by
    intro m
    refine ((hψ.comp (measurable_backlogM' A measurable_id
      (measurable_arrival (i, m)))).indicator
        (measurableSet_lt (measurable_arrival (i, m)) hν)).aemeasurable.congr ?_
    filter_upwards [hgood] with ω hω
    simp only [Set.indicator_apply, mem_setOf_eq, Function.comp_apply, id_eq]
    rw [backlogM_eq hω.1]
  have hmeasI : ∀ m, AEMeasurable (fun ω => ∫⁻ s in Ico (arrival ω (i, m) - ω.1 (i, m))
      (min (arrival ω (i, m)) (ν ω)), ψ (backlogA ω A s)) D.P := by
    intro m
    have hT : Measurable (fun ω : Omega D.M => arrival ω (i, m)) := measurable_arrival (i, m)
    have hTp : Measurable (fun ω : Omega D.M => arrival ω (i, m) - ω.1 (i, m)) :=
      hT.sub ((measurable_pi_apply (i, m)).comp measurable_fst)
    have hJ : Measurable (fun p : Omega D.M × ℝ => {p : Omega D.M × ℝ |
        arrival p.1 (i, m) - p.1.1 (i, m) ≤ p.2 ∧ p.2 < min (arrival p.1 (i, m)) (ν p.1)}.indicator
          (fun p => ψ (backlogM p.1 A p.2)) p) :=
      (hψ.comp (measurable_backlogM' _ measurable_fst measurable_snd)).indicator
        ((measurableSet_le (hTp.comp measurable_fst) measurable_snd).inter
          (measurableSet_lt measurable_snd ((hT.min hν).comp measurable_fst)))
    refine (hJ.lintegral_prod_right' (ν := (volume : Measure ℝ))).aemeasurable.congr ?_
    filter_upwards [hgood] with ω hω
    rw [← lintegral_indicator measurableSet_Ico]
    refine lintegral_congr fun s => ?_
    simp only [Set.indicator_apply, mem_setOf_eq, mem_Ico, backlogM_eq hω.1]
  have h := fun m => asta_dl D A i m ψ hψ ν hν (hνinv m)
  rw [lintegral_tsum hmeasm]
  simp only [h]
  rw [ENNReal.tsum_mul_left, ← lintegral_tsum hmeasI]
  congr 1
  refine lintegral_congr_ae ?_
  filter_upwards [hgood] with ω hω
  exact tsum_pieces (fun k => ω.1 (i, k)) (fun k => hω.2 _)
    (fun t => exists_arr_ge' hω.1 i t) (ν ω) _

/-! ### S3a: service marks (resample `X_j`) and exponential moments -/

/-- Resample the service requirement of job `j`. -/
def usv {M : ℕ} (ω : Omega M) (j : Job M) (x : ℝ) : Omega M := (ω.1, Function.update ω.2.1 j x, ω.2.2)

theorem FinGood_usv {M : ℕ} {ω : Omega M} (hG : FinGood ω) (j : Job M) {x : ℝ} (hx : 0 ≤ x) :
    FinGood (usv ω j x) := by
  refine ⟨fun q => ?_, hG.2⟩
  by_cases hq : q = j
  · subst hq; simp [usv, serviceReq, hx]
  · simp only [serviceReq, usv, Function.update_of_ne hq]; exact hG.1 q

theorem workA_usv {M : ℕ} (ω : Omega M) (j : Job M) (x : ℝ) (A : Job M → Prop) {s t : ℝ}
    (ht : t ≤ arrival ω j) : workA (usv ω j x) A s t = workA ω A s t := by
  unfold workA
  refine tsum_congr (fun q => ?_)
  have ha : arrival (usv ω j x) = arrival ω := rfl
  rw [ha]
  by_cases hq : q = j
  · subst hq
    rw [indicator_of_notMem (fun h => absurd h.2.2 (not_lt.2 ht)),
      indicator_of_notMem (fun h => absurd h.2.2 (not_lt.2 ht))]
  · have hs : serviceReq (usv ω j x) q = serviceReq ω q := by
      simp only [serviceReq, usv, Function.update_of_ne hq]
    by_cases hm : q ∈ {j' : Job M | A j' ∧ s ≤ arrival ω j' ∧ arrival ω j' < t}
    · rw [indicator_of_mem hm, indicator_of_mem hm, hs]
    · rw [indicator_of_notMem hm, indicator_of_notMem hm]

theorem backlogA_usv {M : ℕ} (ω : Omega M) (j : Job M) (x : ℝ) (A : Job M → Prop) {t : ℝ}
    (ht : t ≤ arrival ω j) : backlogA (usv ω j x) A t = backlogA ω A t := by
  unfold backlogA
  congr 2
  refine image_congr (fun s _ => ?_)
  rw [workA_usv ω j x A ht]

/-- **S3a (service mark).** `X_j` is independent of the backlog just before `a_j` and of an
event `B` that ignores `X_j`, so it can be integrated out. -/
theorem service_mark (D : Data) (j : Job D.M) (B : Set (Omega D.M)) (hB : MeasurableSet B)
    (hBinv : ∀ (ω : Omega D.M) (x : ℝ), usv ω j x ∈ B ↔ ω ∈ B) (A : Job D.M → Prop)
    (G : ℝ → ℝ → ENNReal) (hG : Measurable (Function.uncurry G)) :
    ∫⁻ ω, B.indicator (fun ω => G (backlogA ω A (arrival ω j)) (ω.2.1 j)) ω ∂D.P =
      ∫⁻ ω, B.indicator (fun ω => ∫⁻ x, G (backlogA ω A (arrival ω j)) x
        ∂(expMeasure (D.mu j.1))) ω ∂D.P := by
  haveI := P_isProb D
  have hr : 0 < D.mu j.1 := D.mu_pos j.1
  haveI : IsProbabilityMeasure (expMeasure (D.mu j.1)) := isProbabilityMeasure_expMeasure hr
  have hgood := CM4G.ae_good D
  have hT : Measurable (fun ω : Omega D.M => arrival ω j) := measurable_arrival j
  have hbM : Measurable (fun ω : Omega D.M => backlogM ω A (arrival ω j)) :=
    measurable_backlogM' A measurable_id hT
  have hS : Measurable (fun ω : Omega D.M => ω.2.1 j) :=
    (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)
  have hH : Measurable (fun ω : Omega D.M =>
      B.indicator (fun ω => G (backlogM ω A (arrival ω j)) (ω.2.1 j)) ω) :=
    (hG.comp (hbM.prodMk hS)).indicator hB
  have hres : ∫⁻ ω, B.indicator (fun ω => G (backlogM ω A (arrival ω j)) (ω.2.1 j)) ω ∂D.P =
      ∫⁻ ω, ∫⁻ x, B.indicator (fun ω => G (backlogM ω A (arrival ω j)) (ω.2.1 j)) (usv ω j x)
        ∂(expMeasure (D.mu j.1)) ∂D.P := by
    have hmp := P_resampleS D j
    rw [← hmp.lintegral_comp hH]
    exact lintegral_prod_symm _ (hH.comp hmp.measurable).aemeasurable
  calc ∫⁻ ω, B.indicator (fun ω => G (backlogA ω A (arrival ω j)) (ω.2.1 j)) ω ∂D.P
      = ∫⁻ ω, B.indicator (fun ω => G (backlogM ω A (arrival ω j)) (ω.2.1 j)) ω ∂D.P := by
        refine lintegral_congr_ae ?_
        filter_upwards [hgood] with ω hω
        by_cases hω' : ω ∈ B
        · rw [indicator_of_mem hω', indicator_of_mem hω', backlogM_eq hω.1]
        · rw [indicator_of_notMem hω', indicator_of_notMem hω']
    _ = _ := hres
    _ = _ := by
        refine lintegral_congr_ae ?_
        filter_upwards [hgood] with ω hω
        by_cases hω' : ω ∈ B
        · rw [indicator_of_mem hω']
          refine lintegral_congr_ae ?_
          filter_upwards [expMeasure_ae_pos hr] with x hx
          rw [indicator_of_mem ((hBinv ω x).2 hω')]
          have e1 : (usv ω j x).2.1 j = x := by simp [usv]
          have e2 : arrival (usv ω j x) j = arrival ω j := rfl
          rw [e1, e2, backlogM_eq (FinGood_usv hω.1 j hx.le), backlogA_usv ω j x A le_rfl]
        · rw [indicator_of_notMem hω']
          simp only [indicator_of_notMem (mt (hBinv ω _).1 hω'), lintegral_zero]

theorem lintegral_Ico_two_mul {e : ℝ} (he : 0 ≤ e) :
    ∫⁻ s in Ico 0 e, ENNReal.ofReal (2 * s) = ENNReal.ofReal (e ^ 2) := by
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le he,
      intervalIntegral.integral_const_mul, integral_id]
    ring
  · exact (continuous_const.mul continuous_id).integrableOn_Icc.mono_set Ico_subset_Icc_self
  · filter_upwards [ae_restrict_mem measurableSet_Ico] with s hs
    simp only [Pi.zero_apply]; linarith [hs.1]

theorem exp_mean' {r : ℝ} (hr : 0 < r) :
    ∫⁻ x, ENNReal.ofReal x ∂(expMeasure r) = ENNReal.ofReal (1 / r) := by
  have h := exp_mean_lintegral hr
  refine (ENNReal.mul_right_inj (ENNReal.ofReal_pos.2 hr).ne' ENNReal.ofReal_ne_top).1 ?_
  rw [h, ← ENNReal.ofReal_mul hr.le, mul_one_div_cancel hr.ne', ENNReal.ofReal_one]

theorem exp_sq' {r : ℝ} (hr : 0 < r) :
    ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂(expMeasure r) = ENNReal.ofReal (2 / r ^ 2) := by
  have h := CM4C3.exp_asta_core hr (fun s => ENNReal.ofReal (2 * s))
    (ENNReal.measurable_ofReal.comp (measurable_const.mul measurable_id))
  have h2 : ∫⁻ e, (∫⁻ s in Ico 0 e, ENNReal.ofReal (2 * s)) ∂(expMeasure r) =
      ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂(expMeasure r) :=
    lintegral_congr_ae (by
      filter_upwards [expMeasure_ae_pos hr] with e he using lintegral_Ico_two_mul he.le)
  have h1 : ∫⁻ e, ENNReal.ofReal (2 * e) ∂(expMeasure r) = ENNReal.ofReal (2 / r) := by
    simp_rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    rw [lintegral_const_mul _ ENNReal.measurable_ofReal, exp_mean' hr,
      ← ENNReal.ofReal_mul (by norm_num)]
    congr 1; ring
  rw [h2, h1] at h
  refine (ENNReal.mul_right_inj (ENNReal.ofReal_pos.2 hr).ne' ENNReal.ofReal_ne_top).1 ?_
  rw [← h, ← ENNReal.ofReal_mul hr.le]
  congr 1
  field_simp <;> ring

theorem aem_arr (D : Data) (A : Job D.M → Prop) (j : Job D.M) (ψ : ℝ → ENNReal)
    (hψ : Measurable ψ) (ν : Omega D.M → ℝ) (hν : Measurable ν) :
    AEMeasurable (fun ω => {ω : Omega D.M | arrival ω j < ν ω}.indicator
      (fun ω => ψ (backlogA ω A (arrival ω j))) ω) D.P := by
  refine ((hψ.comp (measurable_backlogM' A measurable_id
    (measurable_arrival j))).indicator
      (measurableSet_lt (measurable_arrival j) hν)).aemeasurable.congr ?_
  filter_upwards [CM4G.ae_good D] with ω hω
  simp only [Set.indicator_apply, mem_setOf_eq, Function.comp_apply, id_eq]
  rw [backlogM_eq hω.1]

theorem aem_arr2 (D : Data) (A : Job D.M → Prop) (j : Job D.M) (G : ℝ → ℝ → ENNReal)
    (hG : Measurable (Function.uncurry G)) (ν : Omega D.M → ℝ) (hν : Measurable ν) :
    AEMeasurable (fun ω => {ω : Omega D.M | arrival ω j < ν ω}.indicator
      (fun ω => G (backlogA ω A (arrival ω j)) (ω.2.1 j)) ω) D.P := by
  have hS : Measurable (fun ω : Omega D.M => ω.2.1 j) :=
    (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)
  refine ((hG.comp ((measurable_backlogM' A measurable_id
    (measurable_arrival j)).prodMk hS)).indicator
      (measurableSet_lt (measurable_arrival j) hν)).aemeasurable.congr ?_
  filter_upwards [CM4G.ae_good D] with ω hω
  simp only [Set.indicator_apply, mem_setOf_eq, Function.comp_apply, id_eq, Function.uncurry_apply_pair]
  rw [backlogM_eq hω.1]

/-- **S3 (marked Wald, class `i`).** -/
theorem marked_wald (D : Data) (A : Job D.M → Prop) (i : Fin D.M) (G : ℝ → ℝ → ENNReal)
    (hG : Measurable (Function.uncurry G)) (ν : Omega D.M → ℝ) (hν : Measurable ν)
    (hνinv : ∀ (m : ℕ) (ω : Omega D.M) (x : ℝ), ν (upd ω i m x) = ν ω)
    (hνs : ∀ (j : Job D.M) (ω : Omega D.M) (x : ℝ), ν (usv ω j x) = ν ω) :
    ∫⁻ ω, ∑' m, {ω | arrival ω (i, m) < ν ω}.indicator
        (fun ω => G (backlogA ω A (arrival ω (i, m))) (ω.2.1 (i, m))) ω ∂D.P =
      ENNReal.ofReal (D.lam i) * ∫⁻ ω, (∫⁻ s in Ico 0 (ν ω),
        ∫⁻ x, G (backlogA ω A s) x ∂(expMeasure (D.mu i))) ∂D.P := by
  haveI : IsProbabilityMeasure (expMeasure (D.mu i)) := isProbabilityMeasure_expMeasure (D.mu_pos i)
  have hψ : Measurable (fun v => ∫⁻ x, G v x ∂(expMeasure (D.mu i))) := hG.lintegral_prod_right'
  rw [lintegral_tsum (fun m => aem_arr2 D A (i, m) G hG ν hν)]
  have h := fun m => service_mark D (i, m) {ω | arrival ω (i, m) < ν ω}
    (measurableSet_lt (measurable_arrival _) hν)
    (fun ω x => by simp only [mem_setOf_eq, hνs]; exact Iff.rfl) A G hG
  simp only [h]
  rw [← lintegral_tsum (fun m => aem_arr D A (i, m) _ hψ ν hν)]
  exact arr_wald D A i _ hψ ν hν hνinv

/-- **S2 in ENNReal (p = 1).** `V(t)² + 2∫_0^t V = Σ_{A-jobs a_q<t} [(V(a_q)+X_q)² - V(a_q)²]`. -/
theorem pathwise_enn {M : ℕ} {ω : Omega M} (hG : FinGood ω) (hpos : ∀ j : Job M, 0 ≤ ω.1 j)
    (A : Job M → Prop) (hdist : ∀ q q', A q → A q' → arrival ω q = arrival ω q' → q = q')
    {t : ℝ} (ht : 0 ≤ t) :
    ENNReal.ofReal (backlogA ω A t ^ 2) + 2 * ∫⁻ s in Ico 0 t, ENNReal.ofReal (backlogA ω A s) =
      ∑' q : Job M, {q : Job M | A q ∧ arrival ω q < t}.indicator (fun q =>
        ENNReal.ofReal ((backlogA ω A (arrival ω q) + serviceReq ω q) ^ 2 -
          backlogA ω A (arrival ω q) ^ 2)) q := by
  classical
  have hfin : {q : Job M | A q ∧ arrival ω q < t}.Finite :=
    (hG.2 t).subset (fun q hq => hq.2)
  set F := hfin.toFinset with hF
  have hmem : ∀ q, q ∈ F ↔ A q ∧ arrival ω q < t := fun q => by simp [hF]
  obtain ⟨hii, hid⟩ := CM4S2.pathwise hG hpos A hdist (p := 1) le_rfl F.card t F ht hmem rfl
  simp only [Nat.cast_one, one_add_one_eq_two, pow_one] at hid hii
  have hint : ENNReal.ofReal (∫ s in (0:ℝ)..t, backlogA ω A s) =
      ∫⁻ s in Ico 0 t, ENNReal.ofReal (backlogA ω A s) := by
    rw [intervalIntegral.integral_of_le ht, ofReal_integral_eq_lintegral_ofReal
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht).1 hii)
      (Filter.Eventually.of_forall fun s => backlogA_nonneg ω A s)]
    exact (setLIntegral_congr Ico_ae_eq_Ioc).symm
  have hd : ∀ q ∈ F, 0 ≤ (backlogA ω A (arrival ω q) + serviceReq ω q) ^ 2 -
      backlogA ω A (arrival ω q) ^ 2 := by
    intro q _
    have h1 := backlogA_nonneg ω A (arrival ω q)
    have h2 := hG.1 q
    nlinarith
  have hsum : ∑' q : Job M, {q : Job M | A q ∧ arrival ω q < t}.indicator (fun q =>
      ENNReal.ofReal ((backlogA ω A (arrival ω q) + serviceReq ω q) ^ 2 -
        backlogA ω A (arrival ω q) ^ 2)) q =
      ∑ q ∈ F, ENNReal.ofReal ((backlogA ω A (arrival ω q) + serviceReq ω q) ^ 2 -
        backlogA ω A (arrival ω q) ^ 2) := by
    refine (tsum_eq_sum (s := F) ?_).trans (Finset.sum_congr rfl fun q hq => ?_)
    · intro q hq
      exact indicator_of_notMem (show q ∉ {q : Job M | A q ∧ arrival ω q < t} from fun h => hq ((hmem q).2 h)) _
    · exact indicator_of_mem (show q ∈ {q : Job M | A q ∧ arrival ω q < t} from (hmem q).1 hq) _
  have hI0 : 0 ≤ ∫ s in (0:ℝ)..t, backlogA ω A s :=
    intervalIntegral.integral_nonneg ht (fun s _ => backlogA_nonneg ω A s)
  rw [hsum, ← ENNReal.ofReal_sum_of_nonneg hd, ← hid, ← hint,
    ENNReal.ofReal_add (sq_nonneg _) (by positivity),
    ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat]

end CM4S3

namespace CM4S4
open CoffmanMitrani MeasureTheory ProbabilityTheory Set CM4T CM4M CM4W CM4S1 CM4S3

/-- Finite tiling: the class interarrival pieces `[T_m - e_m, T_m)`, `m ≤ N`, tile `[0, T_N)`. -/
theorem sum_pieces (e : ℕ → ℝ) (he : ∀ k, 0 ≤ e k)
    (hunb : ∀ t, ∃ m, t ≤ ∑ k ∈ Finset.range (m + 1), e k) (N : ℕ) (f : ℝ → ENNReal) :
    ∑ m ∈ Finset.range (N + 1), ∫⁻ s in Ico (∑ k ∈ Finset.range (m + 1), e k - e m)
        (∑ k ∈ Finset.range (m + 1), e k), f s =
      ∫⁻ s in Ico 0 (∑ k ∈ Finset.range (N + 1), e k), f s := by
  rw [← tsum_pieces e he hunb _ f]
  have hS : ∀ m, ∑ k ∈ Finset.range (m + 1), e k - e m = ∑ k ∈ Finset.range m, e k := by
    intro m; rw [Finset.sum_range_succ]; ring
  have hmono : ∀ a b : ℕ, a ≤ b → ∑ k ∈ Finset.range a, e k ≤ ∑ k ∈ Finset.range b, e k :=
    fun a b hab => Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab) (fun k _ _ => he k)
  rw [tsum_eq_sum (s := Finset.range (N + 1))]
  · refine Finset.sum_congr rfl fun m hm => ?_
    rw [min_eq_left (hmono _ _ (by simp only [Finset.mem_range] at hm; omega))]
  · intro m hm
    simp only [Finset.mem_range, not_lt] at hm
    rw [hS, Ico_eq_empty (not_lt.2 ((min_le_right _ _).trans (hmono _ _ hm))),
      Measure.restrict_empty, lintegral_zero_measure]

theorem aem_piece (D : Data) (A : Job D.M → Prop) (j : Job D.M) (ψ : ℝ → ENNReal)
    (hψ : Measurable ψ) :
    AEMeasurable (fun ω => ∫⁻ s in Ico (arrival ω j - ω.1 j) (arrival ω j),
      ψ (backlogA ω A s)) D.P := by
  have hgood := CM4G.ae_good D
  have hT : Measurable (fun ω : Omega D.M => arrival ω j) := measurable_arrival j
  have hTp : Measurable (fun ω : Omega D.M => arrival ω j - ω.1 j) :=
    hT.sub ((measurable_pi_apply j).comp measurable_fst)
  have hJ : Measurable (fun p : Omega D.M × ℝ => {p : Omega D.M × ℝ |
      arrival p.1 j - p.1.1 j ≤ p.2 ∧ p.2 < arrival p.1 j}.indicator
        (fun p => ψ (backlogM p.1 A p.2)) p) :=
    (hψ.comp (measurable_backlogM' _ measurable_fst measurable_snd)).indicator
      ((measurableSet_le (hTp.comp measurable_fst) measurable_snd).inter
        (measurableSet_lt measurable_snd (hT.comp measurable_fst)))
  refine (hJ.lintegral_prod_right' (ν := (volume : Measure ℝ))).aemeasurable.congr ?_
  filter_upwards [hgood] with ω hω
  rw [← lintegral_indicator measurableSet_Ico]
  refine lintegral_congr fun s => ?_
  simp only [Set.indicator_apply, mem_setOf_eq, mem_Ico, backlogM_eq hω.1]

/-- **ASTA summed.** `Σ_{m ≤ N} E ψ(V(T_{c,m})) = λ_c E ∫_0^{T_{c,N}} ψ(V)`. -/
theorem asta_sum (D : Data) (A : Job D.M → Prop) (c : Fin D.M) (N : ℕ) (ψ : ℝ → ENNReal)
    (hψ : Measurable ψ) :
    ∑ m ∈ Finset.range (N + 1), ∫⁻ ω, ψ (backlogA ω A (arrival ω (c, m))) ∂D.P =
      ENNReal.ofReal (D.lam c) *
        ∫⁻ ω, (∫⁻ s in Ico 0 (arrival ω (c, N)), ψ (backlogA ω A s)) ∂D.P := by
  have hgood := CM4G.ae_good D
  rw [Finset.sum_congr rfl fun m _ => asta D A c m ψ hψ, ← Finset.mul_sum,
    ← lintegral_finset_sum' _ (fun m _ => aem_piece D A (c, m) ψ hψ)]
  congr 1
  refine lintegral_congr_ae ?_
  filter_upwards [hgood] with ω hω
  exact sum_pieces (fun k => ω.1 (c, k)) (fun k => hω.2 _) (fun t => exists_arr_ge' hω.1 c t) N _

/-- **Class `c` marks up to `T_{c,N}`** (jobs `m < N`, plus the boundary term at `T_{c,N}`). -/
theorem class_c_part (D : Data) (A : Job D.M → Prop) (c : Fin D.M) (N : ℕ)
    (G : ℝ → ℝ → ENNReal) (hG : Measurable (Function.uncurry G)) :
    ∫⁻ ω, ∑' m, {ω | arrival ω (c, m) < arrival ω (c, N)}.indicator
        (fun ω => G (backlogA ω A (arrival ω (c, m))) (ω.2.1 (c, m))) ω ∂D.P +
      ∫⁻ ω, ∫⁻ x, G (backlogA ω A (arrival ω (c, N))) x ∂(expMeasure (D.mu c)) ∂D.P =
      ENNReal.ofReal (D.lam c) * ∫⁻ ω, (∫⁻ s in Ico 0 (arrival ω (c, N)),
        ∫⁻ x, G (backlogA ω A s) x ∂(expMeasure (D.mu c))) ∂D.P := by
  haveI : IsProbabilityMeasure (expMeasure (D.mu c)) :=
    isProbabilityMeasure_expMeasure (D.mu_pos c)
  have hψ : Measurable (fun v => ∫⁻ x, G v x ∂(expMeasure (D.mu c))) :=
    hG.lintegral_prod_right'
  have hgood := CM4G.ae_good D
  have hinj := CM4S2.ae_arrival_inj D
  have hfin : (fun ω => ∑' m, {ω | arrival ω (c, m) < arrival ω (c, N)}.indicator
        (fun ω => G (backlogA ω A (arrival ω (c, m))) (ω.2.1 (c, m))) ω) =ᵐ[D.P]
      fun ω => ∑ m ∈ Finset.range N, G (backlogA ω A (arrival ω (c, m))) (ω.2.1 (c, m)) := by
    filter_upwards [hgood, hinj] with ω hω hi
    rw [tsum_eq_sum (s := Finset.range N)]
    · refine Finset.sum_congr rfl fun m hm => ?_
      simp only [Finset.mem_range] at hm
      have hle := CM4S1.arrival_mono_idx hω.2 c (show m ≤ N by omega)
      have hne : arrival ω (c, m) ≠ arrival ω (c, N) := fun h => by
        have h2 := hi _ _ h
        simp only [Prod.mk.injEq, true_and] at h2
        omega
      exact indicator_of_mem
        (show ω ∈ {ω | arrival ω (c, m) < arrival ω (c, N)} from lt_of_le_of_ne hle hne) _
    · intro m hm
      simp only [Finset.mem_range, not_lt] at hm
      exact indicator_of_notMem (show ω ∉ {ω | arrival ω (c, m) < arrival ω (c, N)} from
        not_lt.2 (CM4S1.arrival_mono_idx hω.2 c hm)) _
  have hS : ∀ m, Measurable (fun ω : Omega D.M => ω.2.1 (c, m)) := fun m =>
    (measurable_pi_apply (c, m)).comp (measurable_fst.comp measurable_snd)
  have haem : ∀ m, AEMeasurable
      (fun ω => G (backlogA ω A (arrival ω (c, m))) (ω.2.1 (c, m))) D.P := by
    intro m
    refine (aem_arr2 D A (c, m) G hG (fun ω => arrival ω (c, m) + 1)
      ((measurable_arrival _).add_const 1)).congr (Filter.Eventually.of_forall fun ω => ?_)
    exact indicator_of_mem (s := {ω | arrival ω (c, m) < arrival ω (c, m) + 1})
      (by simp only [mem_setOf_eq]; exact lt_add_one _) _
  rw [lintegral_congr_ae hfin, lintegral_finset_sum' _ (fun m _ => haem m)]
  have hs : ∀ m, ∫⁻ ω, G (backlogA ω A (arrival ω (c, m))) (ω.2.1 (c, m)) ∂D.P =
      ∫⁻ ω, ∫⁻ x, G (backlogA ω A (arrival ω (c, m))) x ∂(expMeasure (D.mu c)) ∂D.P := by
    intro m
    have h := service_mark D (c, m) univ MeasurableSet.univ (fun _ _ => by simp) A G hG
    simpa only [indicator_univ] using h
  simp only [hs]
  have h := asta_sum D A c N _ hψ
  rw [Finset.sum_range_succ] at h
  exact h

/-- The second-moment mark `G(v, x) = (v + x)² - v²`. -/
noncomputable def G2 (v x : ℝ) : ENNReal := ENNReal.ofReal ((v + x) ^ 2 - v ^ 2)

theorem measurable_G2 : Measurable (Function.uncurry G2) := by
  show Measurable fun p : ℝ × ℝ => ENNReal.ofReal ((p.1 + p.2) ^ 2 - p.1 ^ 2)
  exact ENNReal.measurable_ofReal.comp (by fun_prop)

/-- **S4 identity (ENNReal).** For `g ∋ c`, `V = backlog of g-jobs`, `ν = T_{c,N}`:
`E[V(ν)² + 2∫_0^ν V] + E Ĝ_c(V(ν)) = Σ_{i∈g} λ_i E ∫_0^ν Ĝ_i(V)`, `Ĝ_i(v) = E_{X~Exp μ_i} G2 v X`. -/
theorem s4_identity (D : Data) (g : Finset (Fin D.M)) (c : Fin D.M) (hc : c ∈ g) (N : ℕ) :
    ∫⁻ ω, (ENNReal.ofReal (backlogA ω (fun q : Job D.M => q.1 ∈ g) (arrival ω (c, N)) ^ 2) +
        2 * ∫⁻ s in Ico 0 (arrival ω (c, N)),
          ENNReal.ofReal (backlogA ω (fun q : Job D.M => q.1 ∈ g) s)) ∂D.P +
      ∫⁻ ω, ∫⁻ x, G2 (backlogA ω (fun q : Job D.M => q.1 ∈ g) (arrival ω (c, N))) x
        ∂(expMeasure (D.mu c)) ∂D.P =
      ∑ i ∈ g, ENNReal.ofReal (D.lam i) * ∫⁻ ω, (∫⁻ s in Ico 0 (arrival ω (c, N)),
        ∫⁻ x, G2 (backlogA ω (fun q : Job D.M => q.1 ∈ g) s) x ∂(expMeasure (D.mu i))) ∂D.P := by
  have hgood := CM4G.ae_good D
  have hinj := CM4S2.ae_arrival_inj D
  have hpath : (fun ω => ENNReal.ofReal (backlogA ω (fun q : Job D.M => q.1 ∈ g)
        (arrival ω (c, N)) ^ 2) + 2 * ∫⁻ s in Ico 0 (arrival ω (c, N)),
          ENNReal.ofReal (backlogA ω (fun q : Job D.M => q.1 ∈ g) s)) =ᵐ[D.P]
      fun ω => ∑ i ∈ g, ∑' m, {ω | arrival ω (i, m) < arrival ω (c, N)}.indicator
        (fun ω => G2 (backlogA ω (fun q : Job D.M => q.1 ∈ g) (arrival ω (i, m)))
          (ω.2.1 (i, m))) ω := by
    filter_upwards [hgood, hinj] with ω hω hi
    rw [pathwise_enn hω.1 hω.2 (fun q : Job D.M => q.1 ∈ g) (fun q q' _ _ h => hi q q' h)
      (t := arrival ω (c, N)) (show 0 ≤ arrival ω (c, N) from
        Finset.sum_nonneg fun k _ => hω.2 _),
      ENNReal.tsum_prod', tsum_fintype, ← Finset.sum_subset (Finset.subset_univ g)]
    · refine Finset.sum_congr rfl fun i hi' => tsum_congr fun m => ?_
      simp only [Set.indicator_apply, mem_setOf_eq, hi', true_and, G2, serviceReq]
    · intro i _ hi'
      exact ENNReal.tsum_eq_zero.2 fun m => indicator_of_notMem (fun h => hi' h.1) _
  rw [lintegral_congr_ae hpath, lintegral_finset_sum' _ (fun i _ =>
    AEMeasurable.ennreal_tsum fun m => aem_arr2 D _ (i, m) G2 measurable_G2 _
      (measurable_arrival (c, N)))]
  rw [← Finset.add_sum_erase g _ hc, ← Finset.add_sum_erase g _ hc, add_right_comm,
    class_c_part D (fun q : Job D.M => q.1 ∈ g) c N G2 measurable_G2]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hic : i ≠ c := Finset.ne_of_mem_erase hi
  exact marked_wald D _ i G2 measurable_G2 (fun ω => arrival ω (c, N)) (measurable_arrival _)
    (fun m ω x => CM4T.arrival_upd_of ω i m x (q := (c, N)) (fun h => absurd h hic.symm)) (fun j ω x => rfl)

end CM4S4

namespace CM4S5
open CoffmanMitrani MeasureTheory ProbabilityTheory Set CM4T CM4M CM4W CM4S1 CM4S3 CM4S4

/-- **S2 in ENNReal, general `p`.** `V(t)^{p+1} + (p+1)∫_0^t V^p = Σ_{A-jobs a_q<t} [(V(a_q)+X_q)^{p+1} - V(a_q)^{p+1}]`. -/
theorem pathwise_enn_p {M : ℕ} {ω : Omega M} (hG : FinGood ω) (hpos : ∀ j : Job M, 0 ≤ ω.1 j)
    (A : Job M → Prop) (hdist : ∀ q q', A q → A q' → arrival ω q = arrival ω q' → q = q')
    {p : ℕ} (hp : 1 ≤ p) {t : ℝ} (ht : 0 ≤ t) :
    ENNReal.ofReal (backlogA ω A t ^ (p + 1)) +
        ENNReal.ofReal ((p : ℝ) + 1) * ∫⁻ s in Ico 0 t, ENNReal.ofReal (backlogA ω A s ^ p) =
      ∑' q : Job M, {q : Job M | A q ∧ arrival ω q < t}.indicator (fun q =>
        ENNReal.ofReal ((backlogA ω A (arrival ω q) + serviceReq ω q) ^ (p + 1) -
          backlogA ω A (arrival ω q) ^ (p + 1))) q := by
  classical
  have hfin : {q : Job M | A q ∧ arrival ω q < t}.Finite :=
    (hG.2 t).subset (fun q hq => hq.2)
  set F := hfin.toFinset with hF
  have hmem : ∀ q, q ∈ F ↔ A q ∧ arrival ω q < t := fun q => by simp [hF]
  obtain ⟨hii, hid⟩ := CM4S2.pathwise hG hpos A hdist hp F.card t F ht hmem rfl
  have hint : ENNReal.ofReal (∫ s in (0:ℝ)..t, backlogA ω A s ^ p) =
      ∫⁻ s in Ico 0 t, ENNReal.ofReal (backlogA ω A s ^ p) := by
    rw [intervalIntegral.integral_of_le ht, ofReal_integral_eq_lintegral_ofReal
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht).1 hii)
      (Filter.Eventually.of_forall fun s => pow_nonneg (backlogA_nonneg ω A s) p)]
    exact (setLIntegral_congr Ico_ae_eq_Ioc).symm
  have hd : ∀ q ∈ F, 0 ≤ (backlogA ω A (arrival ω q) + serviceReq ω q) ^ (p + 1) -
      backlogA ω A (arrival ω q) ^ (p + 1) := by
    intro q _
    have h1 := backlogA_nonneg ω A (arrival ω q)
    have h2 := hG.1 q
    have h3 := pow_le_pow_left₀ h1 (le_add_of_nonneg_right h2) (p + 1)
    linarith
  have hsum : ∑' q : Job M, {q : Job M | A q ∧ arrival ω q < t}.indicator (fun q =>
      ENNReal.ofReal ((backlogA ω A (arrival ω q) + serviceReq ω q) ^ (p + 1) -
        backlogA ω A (arrival ω q) ^ (p + 1))) q =
      ∑ q ∈ F, ENNReal.ofReal ((backlogA ω A (arrival ω q) + serviceReq ω q) ^ (p + 1) -
        backlogA ω A (arrival ω q) ^ (p + 1)) := by
    refine (tsum_eq_sum (s := F) ?_).trans (Finset.sum_congr rfl fun q hq => ?_)
    · intro q hq
      exact indicator_of_notMem (show q ∉ {q : Job M | A q ∧ arrival ω q < t} from
        fun h => hq ((hmem q).2 h)) _
    · exact indicator_of_mem (show q ∈ {q : Job M | A q ∧ arrival ω q < t} from (hmem q).1 hq) _
  have hI0 : 0 ≤ ∫ s in (0:ℝ)..t, backlogA ω A s ^ p :=
    intervalIntegral.integral_nonneg ht (fun s _ => pow_nonneg (backlogA_nonneg ω A s) p)
  rw [hsum, ← ENNReal.ofReal_sum_of_nonneg hd, ← hid, ← hint,
    ENNReal.ofReal_add (pow_nonneg (backlogA_nonneg ω A t) _) (mul_nonneg (by positivity) hI0),
    ENNReal.ofReal_mul (by positivity)]

/-- The `(p+1)`-st moment mark `G(v, x) = (v + x)^{p+1} - v^{p+1}`. -/
noncomputable def Gp (p : ℕ) (v x : ℝ) : ENNReal :=
  ENNReal.ofReal ((v + x) ^ (p + 1) - v ^ (p + 1))

theorem measurable_Gp (p : ℕ) : Measurable (Function.uncurry (Gp p)) := by
  show Measurable fun q : ℝ × ℝ => ENNReal.ofReal ((q.1 + q.2) ^ (p + 1) - q.1 ^ (p + 1))
  exact ENNReal.measurable_ofReal.comp (by fun_prop)

/-- **S4 inequality, general `p` and any job set `A` inside the classes `g`.** -/
theorem s4_le (D : Data) (g : Finset (Fin D.M)) (c : Fin D.M) (hc : c ∈ g) (N : ℕ)
    {p : ℕ} (hp : 1 ≤ p) (A : Job D.M → Prop) (hA : ∀ q, A q → q.1 ∈ g) :
    ∫⁻ ω, (ENNReal.ofReal (backlogA ω A (arrival ω (c, N)) ^ (p + 1)) +
        ENNReal.ofReal ((p : ℝ) + 1) * ∫⁻ s in Ico 0 (arrival ω (c, N)),
          ENNReal.ofReal (backlogA ω A s ^ p)) ∂D.P +
      ∫⁻ ω, ∫⁻ x, Gp p (backlogA ω A (arrival ω (c, N))) x ∂(expMeasure (D.mu c)) ∂D.P ≤
      ∑ i ∈ g, ENNReal.ofReal (D.lam i) * ∫⁻ ω, (∫⁻ s in Ico 0 (arrival ω (c, N)),
        ∫⁻ x, Gp p (backlogA ω A s) x ∂(expMeasure (D.mu i))) ∂D.P := by
  have hgood := CM4G.ae_good D
  have hinj := CM4S2.ae_arrival_inj D
  have hpath : (fun ω => ENNReal.ofReal (backlogA ω A (arrival ω (c, N)) ^ (p + 1)) +
        ENNReal.ofReal ((p : ℝ) + 1) * ∫⁻ s in Ico 0 (arrival ω (c, N)),
          ENNReal.ofReal (backlogA ω A s ^ p)) ≤ᵐ[D.P]
      fun ω => ∑ i ∈ g, ∑' m, {ω | arrival ω (i, m) < arrival ω (c, N)}.indicator
        (fun ω => Gp p (backlogA ω A (arrival ω (i, m))) (ω.2.1 (i, m))) ω := by
    filter_upwards [hgood, hinj] with ω hω hi
    rw [pathwise_enn_p hω.1 hω.2 A (fun q q' _ _ h => hi q q' h) hp
      (t := arrival ω (c, N)) (show 0 ≤ arrival ω (c, N) from
        Finset.sum_nonneg fun k _ => hω.2 _),
      ENNReal.tsum_prod', tsum_fintype, ← Finset.sum_subset (Finset.subset_univ g)]
    · refine Finset.sum_le_sum fun i _ => ENNReal.tsum_le_tsum fun m => ?_
      classical
      by_cases hAq : A (i, m)
      · rw [Set.indicator_apply, Set.indicator_apply]
        simp [hAq, Gp, serviceReq]
      · rw [Set.indicator_apply]
        simp [hAq]
    · intro i _ hi'
      exact ENNReal.tsum_eq_zero.2 fun m => indicator_of_notMem (fun h => hi' (hA _ h.1)) _
  refine (add_le_add (lintegral_mono_ae hpath) le_rfl).trans_eq ?_
  rw [lintegral_finset_sum' _ (fun i _ =>
    AEMeasurable.ennreal_tsum fun m => aem_arr2 D A (i, m) (Gp p) (measurable_Gp p) _
      (measurable_arrival (c, N)))]
  rw [← Finset.add_sum_erase g _ hc, ← Finset.add_sum_erase g _ hc, add_right_comm,
    class_c_part D A c N (Gp p) (measurable_Gp p)]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hic : i ≠ c := Finset.ne_of_mem_erase hi
  exact marked_wald D A i (Gp p) (measurable_Gp p) (fun ω => arrival ω (c, N))
    (measurable_arrival _)
    (fun m ω x => CM4T.arrival_upd_of ω i m x (q := (c, N)) (fun h => absurd h hic.symm))
    (fun j ω x => rfl)

end CM4S5

namespace CM4S6
open CoffmanMitrani MeasureTheory ProbabilityTheory Set CM4T CM4M CM4W CM4S1 CM4S3 CM4S4 CM4S5

theorem lintegral_Ico_three_sq {e : ℝ} (he : 0 ≤ e) :
    ∫⁻ s in Ico 0 e, ENNReal.ofReal (3 * s ^ 2) = ENNReal.ofReal (e ^ 3) := by
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le he,
      intervalIntegral.integral_const_mul, integral_pow]
    ring
  · exact (continuous_const.mul (continuous_pow 2)).integrableOn_Icc.mono_set Ico_subset_Icc_self
  · filter_upwards [ae_restrict_mem measurableSet_Ico] with s hs
    simp only [Pi.zero_apply]; positivity

theorem exp_cube' {r : ℝ} (hr : 0 < r) :
    ∫⁻ x, ENNReal.ofReal (x ^ 3) ∂(expMeasure r) = ENNReal.ofReal (6 / r ^ 3) := by
  have h := CM4C3.exp_asta_core hr (fun s => ENNReal.ofReal (3 * s ^ 2))
    (ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_id.pow_const 2)))
  have h2 : ∫⁻ e, (∫⁻ s in Ico 0 e, ENNReal.ofReal (3 * s ^ 2)) ∂(expMeasure r) =
      ∫⁻ x, ENNReal.ofReal (x ^ 3) ∂(expMeasure r) :=
    lintegral_congr_ae (by
      filter_upwards [expMeasure_ae_pos hr] with e he using lintegral_Ico_three_sq he.le)
  have h1 : ∫⁻ e, ENNReal.ofReal (3 * e ^ 2) ∂(expMeasure r) = ENNReal.ofReal (6 / r ^ 2) := by
    simp_rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3)]
    rw [lintegral_const_mul _ (by fun_prop : Measurable fun e : ℝ => ENNReal.ofReal (e ^ 2)),
      exp_sq' hr, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1; ring
  rw [h2, h1] at h
  refine (ENNReal.mul_right_inj (ENNReal.ofReal_pos.2 hr).ne' ENNReal.ofReal_ne_top).1 ?_
  rw [← h, ← ENNReal.ofReal_mul hr.le]
  congr 1
  field_simp

end CM4S6

namespace CM4S7
open CoffmanMitrani MeasureTheory ProbabilityTheory Set CM4T CM4M CM4W CM4S1 CM4S3 CM4S4 CM4S5 CM4S6

theorem G2_eq_Gp (v x : ℝ) : G2 v x = Gp 1 v x := by
  unfold G2 Gp; norm_num

/-- **S5a, p = 1**: `E_X[(v+X)^2 - v^2] = 2v/μ + 2/μ²`. -/
theorem Gp_one_hat {r v : ℝ} (hr : 0 < r) (hv : 0 ≤ v) :
    ∫⁻ x, Gp 1 v x ∂(expMeasure r) = ENNReal.ofReal (2 * v / r + 2 / r ^ 2) := by
  have h : ∀ᵐ x ∂(expMeasure r), Gp 1 v x =
      ENNReal.ofReal (2 * v) * ENNReal.ofReal x + ENNReal.ofReal (x ^ 2) := by
    filter_upwards [expMeasure_ae_pos hr] with x hx
    unfold Gp
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1; ring
  rw [lintegral_congr_ae h, lintegral_add_left (ENNReal.measurable_ofReal.const_mul _),
    lintegral_const_mul _ ENNReal.measurable_ofReal, exp_mean' hr, exp_sq' hr,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; ring

/-- **S5a, p = 2**: `E_X[(v+X)^3 - v^3] = 3v²/μ + 6v/μ² + 6/μ³`. -/
theorem Gp_two_hat {r v : ℝ} (hr : 0 < r) (hv : 0 ≤ v) :
    ∫⁻ x, Gp 2 v x ∂(expMeasure r) =
      ENNReal.ofReal (3 * v ^ 2 / r + 6 * v / r ^ 2 + 6 / r ^ 3) := by
  have h : ∀ᵐ x ∂(expMeasure r), Gp 2 v x =
      ENNReal.ofReal (3 * v ^ 2) * ENNReal.ofReal x +
        (ENNReal.ofReal (3 * v) * ENNReal.ofReal (x ^ 2) + ENNReal.ofReal (x ^ 3)) := by
    filter_upwards [expMeasure_ae_pos hr] with x hx
    unfold Gp
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1; ring
  have hm2 : Measurable fun x : ℝ => ENNReal.ofReal (x ^ 2) :=
    ENNReal.measurable_ofReal.comp (measurable_id.pow_const 2)
  rw [lintegral_congr_ae h, lintegral_add_left (ENNReal.measurable_ofReal.const_mul _),
    lintegral_add_left (hm2.const_mul _),
    lintegral_const_mul _ ENNReal.measurable_ofReal, lintegral_const_mul _ hm2,
    exp_mean' hr, exp_sq' hr, exp_cube' hr,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; ring

theorem exp_mom_lt_top {r : ℝ} (hr : 0 < r) {k : ℕ} (hk : k ≤ 3) :
    ∫⁻ x, ENNReal.ofReal (x ^ k) ∂(expMeasure r) < ⊤ := by
  haveI := isProbabilityMeasure_expMeasure hr
  interval_cases k
  · simp
  · simp only [pow_one]; rw [exp_mean' hr]; exact ENNReal.ofReal_lt_top
  · rw [exp_sq' hr]; exact ENNReal.ofReal_lt_top
  · rw [exp_cube' hr]; exact ENNReal.ofReal_lt_top

/-- Marginal of an interarrival coordinate. -/
theorem lintegral_inter (D : Data) (j : Job D.M) {f : ℝ → ENNReal} (hf : Measurable f) :
    ∫⁻ ω, f (ω.1 j) ∂D.P = ∫⁻ x, f x ∂(expMeasure (D.lam j.1)) := by
  haveI : ∀ j : Job D.M, IsProbabilityMeasure (expMeasure (D.lam j.1)) :=
    fun j => isProbabilityMeasure_expMeasure (D.lam_pos j.1)
  haveI : ∀ j : Job D.M, IsProbabilityMeasure (expMeasure (D.mu j.1)) :=
    fun j => isProbabilityMeasure_expMeasure (D.mu_pos j.1)
  have hmeas : Measurable fun ω : Omega D.M => ω.1 j :=
    (measurable_pi_apply j).comp measurable_fst
  have hmap : D.P.map (fun ω : Omega D.M => ω.1 j) = expMeasure (D.lam j.1) := by
    have : (fun ω : Omega D.M => ω.1 j) = (fun x : Job D.M → ℝ => x j) ∘ Prod.fst := rfl
    rw [this, ← Measure.map_map (measurable_pi_apply j) measurable_fst]
    unfold Data.P
    rw [Measure.map_fst_prod, measure_univ, one_smul, Measure.infinitePi_map_eval]
  rw [← hmap, lintegral_map hf hmeas]

/-- Marginal of a service coordinate. -/
theorem lintegral_serv (D : Data) (j : Job D.M) {f : ℝ → ENNReal} (hf : Measurable f) :
    ∫⁻ ω, f (ω.2.1 j) ∂D.P = ∫⁻ x, f x ∂(expMeasure (D.mu j.1)) := by
  haveI : ∀ j : Job D.M, IsProbabilityMeasure (expMeasure (D.lam j.1)) :=
    fun j => isProbabilityMeasure_expMeasure (D.lam_pos j.1)
  haveI : ∀ j : Job D.M, IsProbabilityMeasure (expMeasure (D.mu j.1)) :=
    fun j => isProbabilityMeasure_expMeasure (D.mu_pos j.1)
  have hmeas : Measurable fun ω : Omega D.M => ω.2.1 j :=
    (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)
  have hmap : D.P.map (fun ω : Omega D.M => ω.2.1 j) = expMeasure (D.mu j.1) := by
    have : (fun ω : Omega D.M => ω.2.1 j) =
        (fun x : Job D.M → ℝ => x j) ∘ Prod.fst ∘ Prod.snd := rfl
    rw [this, ← Measure.map_map (measurable_pi_apply j) (measurable_fst.comp measurable_snd),
      ← Measure.map_map measurable_fst measurable_snd]
    unfold Data.P
    rw [Measure.map_snd_prod, measure_univ, one_smul, Measure.map_fst_prod, measure_univ,
      one_smul, Measure.infinitePi_map_eval]
  rw [← hmap, lintegral_map hf hmeas]

theorem mom_inter_lt_top (D : Data) (j : Job D.M) {k : ℕ} (hk : k ≤ 3) :
    ∫⁻ ω, ENNReal.ofReal (ω.1 j ^ k) ∂D.P < ⊤ := by
  have h := lintegral_inter D j (f := fun x => ENNReal.ofReal (x ^ k))
    (ENNReal.measurable_ofReal.comp (measurable_id.pow_const k))
  exact h ▸ exp_mom_lt_top (D.lam_pos j.1) hk

theorem mom_serv_lt_top (D : Data) (j : Job D.M) {k : ℕ} (hk : k ≤ 3) :
    ∫⁻ ω, ENNReal.ofReal (ω.2.1 j ^ k) ∂D.P < ⊤ := by
  have h := lintegral_serv D j (f := fun x => ENNReal.ofReal (x ^ k))
    (ENNReal.measurable_ofReal.comp (measurable_id.pow_const k))
  exact h ▸ exp_mom_lt_top (D.mu_pos j.1) hk

/-- The backlog of a finite job set is at most its total work. -/
theorem backlogA_le_sum {M : ℕ} {ω : Omega M} (hG : FinGood ω) {A : Job M → Prop}
    (S : Finset (Job M)) (hS : ∀ q, A q → q ∈ S) (t : ℝ) :
    backlogA ω A t ≤ ∑ q ∈ S, ω.2.1 q := by
  have hY : 0 ≤ ∑ q ∈ S, ω.2.1 q := Finset.sum_nonneg fun q _ => hG.1 q
  unfold backlogA
  refine max_le hY (Real.sSup_le ?_ hY)
  rintro _ ⟨s, hs, rfl⟩
  have hw : workA ω A s t ≤ ∑ q ∈ S, ω.2.1 q := by
    unfold workA
    rw [tsum_eq_sum (s := S) (fun q hq => indicator_of_notMem (fun h => hq (hS q h.1)) _)]
    refine Finset.sum_le_sum fun q _ => ?_
    by_cases h : q ∈ {j : Job M | A j ∧ s ≤ arrival ω j ∧ arrival ω j < t}
    · rw [indicator_of_mem h]; exact le_rfl
    · rw [indicator_of_notMem h]; exact hG.1 q
  linarith [hs.2]

/-- **S5b(i)**: for a job set inside a finite set, `E ∫_0^{T_{c,N}} V^p < ∞` (p ≤ 2). -/
theorem fin_trunc (D : Data) {A : Job D.M → Prop} (S : Finset (Job D.M))
    (hS : ∀ q, A q → q ∈ S) (c : Fin D.M) (N p : ℕ) (hp : p ≤ 2) :
    ∫⁻ ω, (∫⁻ s in Ico 0 (arrival ω (c, N)), ENNReal.ofReal (backlogA ω A s ^ p)) ∂D.P < ⊤ := by
  have hgood := CM4G.ae_good D
  let R : Omega D.M → ENNReal := fun ω =>
    ENNReal.ofReal (((N : ℝ) + 1) ^ p) *
        ∑ m ∈ Finset.range (N + 1), ENNReal.ofReal (ω.1 (c, m) ^ (p + 1)) +
      ENNReal.ofReal ((S.card : ℝ) ^ p) * ∑ q ∈ S, ENNReal.ofReal (ω.2.1 q ^ (p + 1))
  have hle : ∀ᵐ ω ∂D.P,
      (∫⁻ s in Ico 0 (arrival ω (c, N)), ENNReal.ofReal (backlogA ω A s ^ p)) ≤ R ω := by
    filter_upwards [hgood] with ω hω
    obtain ⟨hG, hpos⟩ := hω
    have hT0 : 0 ≤ arrival ω (c, N) := Finset.sum_nonneg fun m _ => hpos _
    have hY0 : 0 ≤ ∑ q ∈ S, ω.2.1 q := Finset.sum_nonneg fun q _ => hG.1 q
    have h1 : (∫⁻ s in Ico 0 (arrival ω (c, N)), ENNReal.ofReal (backlogA ω A s ^ p)) ≤
        ENNReal.ofReal (arrival ω (c, N) * (∑ q ∈ S, ω.2.1 q) ^ p) := by
      calc (∫⁻ s in Ico 0 (arrival ω (c, N)), ENNReal.ofReal (backlogA ω A s ^ p))
          ≤ ∫⁻ s in Ico 0 (arrival ω (c, N)), ENNReal.ofReal ((∑ q ∈ S, ω.2.1 q) ^ p) :=
            lintegral_mono fun s => ENNReal.ofReal_le_ofReal
              (pow_le_pow_left₀ (backlogA_nonneg ω A s) (backlogA_le_sum hG S hS s) p)
        _ = ENNReal.ofReal (arrival ω (c, N) * (∑ q ∈ S, ω.2.1 q) ^ p) := by
            rw [setLIntegral_const, Real.volume_Ico, sub_zero, mul_comm,
              ← ENNReal.ofReal_mul hT0]
    have hyoung : ∀ T Y : ℝ, 0 ≤ T → 0 ≤ Y → T * Y ^ p ≤ T ^ (p + 1) + Y ^ (p + 1) := by
      intro T Y hT hY
      rcases le_total T Y with h | h
      · have : T * Y ^ p ≤ Y ^ (p + 1) := by
          rw [pow_succ']; exact mul_le_mul_of_nonneg_right h (pow_nonneg hY _)
        linarith [pow_nonneg hT (p + 1)]
      · have : T * Y ^ p ≤ T ^ (p + 1) := by
          rw [pow_succ']; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hY h p) hT
        linarith [pow_nonneg hY (p + 1)]
    have hTj : arrival ω (c, N) ^ (p + 1) ≤
        ((N : ℝ) + 1) ^ p * ∑ m ∈ Finset.range (N + 1), ω.1 (c, m) ^ (p + 1) := by
      have := pow_sum_le_card_mul_sum_pow (s := Finset.range (N + 1))
        (f := fun m => ω.1 (c, m)) (fun m _ => hpos _) p
      simpa [arrival] using this
    have hYj : (∑ q ∈ S, ω.2.1 q) ^ (p + 1) ≤ (S.card : ℝ) ^ p * ∑ q ∈ S, ω.2.1 q ^ (p + 1) :=
      pow_sum_le_card_mul_sum_pow (fun q _ => hG.1 q) p
    have hs1 : 0 ≤ ∑ m ∈ Finset.range (N + 1), ω.1 (c, m) ^ (p + 1) :=
      Finset.sum_nonneg fun m _ => pow_nonneg (hpos _) _
    have hs2 : 0 ≤ ∑ q ∈ S, ω.2.1 q ^ (p + 1) :=
      Finset.sum_nonneg fun q _ => pow_nonneg (hG.1 q) _
    refine h1.trans ?_
    show _ ≤ ENNReal.ofReal (((N : ℝ) + 1) ^ p) *
        ∑ m ∈ Finset.range (N + 1), ENNReal.ofReal (ω.1 (c, m) ^ (p + 1)) +
      ENNReal.ofReal ((S.card : ℝ) ^ p) * ∑ q ∈ S, ENNReal.ofReal (ω.2.1 q ^ (p + 1))
    rw [← ENNReal.ofReal_sum_of_nonneg (fun m _ => pow_nonneg (hpos _) _),
      ← ENNReal.ofReal_sum_of_nonneg (fun q _ => pow_nonneg (show 0 ≤ ω.2.1 q from hG.1 q) _),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (mul_nonneg (by positivity) hs1) (mul_nonneg (by positivity) hs2)]
    exact ENNReal.ofReal_le_ofReal
      ((hyoung _ _ hT0 hY0).trans (add_le_add hTj hYj))
  refine lt_of_le_of_lt (lintegral_mono_ae hle) ?_
  have hm1 : ∀ j : Job D.M, Measurable fun ω : Omega D.M => ENNReal.ofReal (ω.1 j ^ (p + 1)) :=
    fun j => ENNReal.measurable_ofReal.comp
      (((measurable_pi_apply j).comp measurable_fst).pow_const _)
  have hm2 : ∀ j : Job D.M, Measurable fun ω : Omega D.M => ENNReal.ofReal (ω.2.1 j ^ (p + 1)) :=
    fun j => ENNReal.measurable_ofReal.comp
      (((measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)).pow_const _)
  show ∫⁻ ω, (ENNReal.ofReal (((N : ℝ) + 1) ^ p) *
        ∑ m ∈ Finset.range (N + 1), ENNReal.ofReal (ω.1 (c, m) ^ (p + 1)) +
      ENNReal.ofReal ((S.card : ℝ) ^ p) * ∑ q ∈ S, ENNReal.ofReal (ω.2.1 q ^ (p + 1))) ∂D.P < ⊤
  rw [lintegral_add_left ((Finset.measurable_sum _ fun m _ => hm1 _).const_mul _),
    lintegral_const_mul _ (Finset.measurable_sum _ fun m _ => hm1 _),
    lintegral_const_mul _ (Finset.measurable_sum _ fun q _ => hm2 _),
    lintegral_finsetSum _ (fun m _ => hm1 _), lintegral_finsetSum _ (fun q _ => hm2 _)]
  exact ENNReal.add_lt_top.2
    ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.sum_lt_top.2 fun m _ => mom_inter_lt_top D _ (by omega)),
     ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.sum_lt_top.2 fun q _ => mom_serv_lt_top D _ (by omega))⟩

end CM4S7

namespace CM4S8
open CoffmanMitrani MeasureTheory ProbabilityTheory Set CM4T CM4M CM4W CM4S1 CM4S3 CM4S4 CM4S5 CM4S6 CM4S7

/-- `E T_{c,N} = (N+1)/λ_c`. -/
theorem ET_arr (D : Data) (c : Fin D.M) (N : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (arrival ω (c, N)) ∂D.P = ENNReal.ofReal ((N + 1) / D.lam c) := by
  have hgood := CM4G.ae_good D
  have h : ∀ᵐ ω ∂D.P, ENNReal.ofReal (arrival ω (c, N)) =
      ∑ m ∈ Finset.range (N + 1), ENNReal.ofReal (ω.1 (c, m)) := by
    filter_upwards [hgood] with ω hω
    exact ENNReal.ofReal_sum_of_nonneg fun m _ => hω.2 _
  have hm : ∀ j : Job D.M, Measurable fun ω : Omega D.M => ENNReal.ofReal (ω.1 j) :=
    fun j => ENNReal.measurable_ofReal.comp ((measurable_pi_apply j).comp measurable_fst)
  rw [lintegral_congr_ae h, lintegral_finsetSum _ fun m _ => hm _]
  have h1 : ∀ m, ∫⁻ ω, ENNReal.ofReal (ω.1 (c, m)) ∂D.P = ENNReal.ofReal (1 / D.lam c) :=
    fun m => (lintegral_inter D (c, m) ENNReal.measurable_ofReal).trans (exp_mean' (D.lam_pos c))
  have hl := D.lam_pos c
  rw [Finset.sum_congr rfl fun m _ => h1 m, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  congr 1; push_cast; ring

theorem inner_hat1 {r : ℝ} (hr : 0 < r) {M : ℕ} (ω : Omega M) (A : Job M → Prop) (T : ℝ) :
    ∫⁻ s in Ico 0 T, ∫⁻ x, Gp 1 (backlogA ω A s) x ∂(expMeasure r) =
      ENNReal.ofReal (2 / r) * (∫⁻ s in Ico 0 T, ENNReal.ofReal (backlogA ω A s ^ 1)) +
        ENNReal.ofReal (2 / r ^ 2) * ENNReal.ofReal T := by
  have h : ∀ s, ∫⁻ x, Gp 1 (backlogA ω A s) x ∂(expMeasure r) =
      ENNReal.ofReal (2 / r) * ENNReal.ofReal (backlogA ω A s ^ 1) +
        ENNReal.ofReal (2 / r ^ 2) := by
    intro s
    have hv := backlogA_nonneg ω A s
    rw [Gp_one_hat hr hv, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1; ring
  simp_rw [h]
  rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    setLIntegral_const, Real.volume_Ico, sub_zero]

/-- **S5b(ii)**: the uniform first-moment bound for a finite job set inside the classes `g`:
`(1-ρ_g) E∫_0^{T_{c,N}} V ≤ K_g (N+1)/λ_c`. -/
theorem s5_bound1 (D : Data) (g : Finset (Fin D.M)) (c : Fin D.M) (hc : c ∈ g) (N : ℕ)
    (A : Job D.M → Prop) (hA : ∀ q, A q → q.1 ∈ g) (S : Finset (Job D.M))
    (hS : ∀ q, A q → q ∈ S) :
    (∫⁻ ω, (∫⁻ s in Ico 0 (arrival ω (c, N)), ENNReal.ofReal (backlogA ω A s ^ 1)) ∂D.P).toReal *
        (1 - ∑ i ∈ g, D.lam i / D.mu i) ≤
      (∑ i ∈ g, D.lam i / D.mu i ^ 2) * ((N + 1) / D.lam c) := by
  have hgood := CM4G.ae_good D
  have hJtop := (fin_trunc D S hS c N 1 (by norm_num)).ne
  obtain ⟨j, hj0, hJj⟩ : ∃ j : ℝ, 0 ≤ j ∧
      (∫⁻ ω, (∫⁻ s in Ico 0 (arrival ω (c, N)), ENNReal.ofReal (backlogA ω A s ^ 1)) ∂D.P) =
        ENNReal.ofReal j :=
    ⟨_, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hJtop).symm⟩
  have hs4 := s4_le D g c hc N (p := 1) le_rfl A hA
  have hl := D.lam_pos c
  have hR : ∀ i ∈ g, ENNReal.ofReal (D.lam i) * ∫⁻ ω, (∫⁻ s in Ico 0 (arrival ω (c, N)),
        ∫⁻ x, Gp 1 (backlogA ω A s) x ∂(expMeasure (D.mu i))) ∂D.P =
      ENNReal.ofReal (D.lam i * (2 / D.mu i * j + 2 / D.mu i ^ 2 * ((N + 1) / D.lam c))) := by
    intro i _
    have hmu := D.mu_pos i
    have hli := D.lam_pos i
    have h1 : ∀ ω : Omega D.M, (∫⁻ s in Ico 0 (arrival ω (c, N)),
          ∫⁻ x, Gp 1 (backlogA ω A s) x ∂(expMeasure (D.mu i))) =
        ENNReal.ofReal (2 / D.mu i) *
            (∫⁻ s in Ico 0 (arrival ω (c, N)), ENNReal.ofReal (backlogA ω A s ^ 1)) +
          ENNReal.ofReal (2 / D.mu i ^ 2) * ENNReal.ofReal (arrival ω (c, N)) :=
      fun ω => inner_hat1 hmu ω A _
    have hTm : Measurable fun ω : Omega D.M => ENNReal.ofReal (arrival ω (c, N)) :=
      ENNReal.measurable_ofReal.comp (measurable_arrival _)
    rw [lintegral_congr fun ω => h1 ω, lintegral_add_right _ (hTm.const_mul _),
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul _ hTm, ET_arr, hJj,
      ENNReal.ofReal_mul hli.le, ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
  have hmain : ENNReal.ofReal 2 * ENNReal.ofReal j ≤
      ∑ i ∈ g, ENNReal.ofReal (D.lam i * (2 / D.mu i * j + 2 / D.mu i ^ 2 * ((N + 1) / D.lam c))) := by
    refine le_trans ?_ (le_of_eq (Finset.sum_congr rfl hR))
    rw [← hJj]
    refine le_trans ?_ hs4
    refine le_trans ?_ le_self_add
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun ω => le_trans ?_ le_add_self
    norm_num
  have hnn : ∀ i ∈ g, 0 ≤ D.lam i * (2 / D.mu i * j + 2 / D.mu i ^ 2 * ((N + 1) / D.lam c)) := by
    intro i _
    have := D.lam_pos i
    have := D.mu_pos i
    positivity
  rw [← ENNReal.ofReal_mul zero_le_two, ← ENNReal.ofReal_sum_of_nonneg hnn,
    ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg hnn)] at hmain
  rw [hJj, ENNReal.toReal_ofReal hj0]
  have e : ∑ i ∈ g, D.lam i * (2 / D.mu i * j + 2 / D.mu i ^ 2 * ((N + 1) / D.lam c)) =
      2 * j * ∑ i ∈ g, D.lam i / D.mu i +
        2 * (∑ i ∈ g, D.lam i / D.mu i ^ 2) * ((N + 1) / D.lam c) := by
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := (D.mu_pos i).ne'
    field_simp
  rw [e] at hmain
  linear_combination (1 / 2 : ℝ) * hmain

end CM4S8

namespace CM4S9
open CoffmanMitrani MeasureTheory ProbabilityTheory Set CM4T CM4M CM4W CM4S1 CM4S3 CM4S4 CM4S5 CM4S6
  CM4S7 CM4S8

/-- Class-`g` jobs of index `< n`. -/
def An {M : ℕ} (g : Finset (Fin M)) (n : ℕ) : Job M → Prop := fun q => q.1 ∈ g ∧ q.2 < n

theorem aem_full (D : Data) (A : Job D.M → Prop) (c : Fin D.M) (N : ℕ) (ψ : ℝ → ENNReal)
    (hψ : Measurable ψ) :
    AEMeasurable (fun ω => ∫⁻ s in Ico 0 (arrival ω (c, N)), ψ (backlogA ω A s)) D.P := by
  have hgood := CM4G.ae_good D
  have hT : Measurable (fun ω : Omega D.M => arrival ω (c, N)) := measurable_arrival _
  have hJ : Measurable (fun p : Omega D.M × ℝ => {p : Omega D.M × ℝ |
      0 ≤ p.2 ∧ p.2 < arrival p.1 (c, N)}.indicator
        (fun p => ψ (backlogM p.1 A p.2)) p) :=
    (hψ.comp (measurable_backlogM' _ measurable_fst measurable_snd)).indicator
      ((measurableSet_le measurable_const measurable_snd).inter
        (measurableSet_lt measurable_snd (hT.comp measurable_fst)))
  refine (hJ.lintegral_prod_right' (ν := (volume : Measure ℝ))).aemeasurable.congr ?_
  filter_upwards [hgood] with ω hω
  rw [← lintegral_indicator measurableSet_Ico]
  refine lintegral_congr fun s => ?_
  simp only [Set.indicator_apply, mem_setOf_eq, mem_Ico, backlogM_eq hω.1]

theorem trunc_lim {M : ℕ} {ω : Omega M} (hG : FinGood ω) (g : Finset (Fin M)) (s : ℝ) :
    ∃ n, backlogA ω (An g n) s = backlogA ω (fun q => q.1 ∈ g) s := by
  obtain ⟨n, hn⟩ : ∃ n, ∀ q ∈ (hG.2 s).toFinset, q.2 < n :=
    ⟨(hG.2 s).toFinset.sup (fun q => q.2) + 1,
      fun q hq => Nat.lt_succ_of_le (Finset.le_sup (f := fun q : Job M => q.2) hq)⟩
  refine ⟨n, (backlogA_eq_of ω (fun q hq => hq.1) (fun q hA hn' => ?_)).symm⟩
  by_contra hlt
  push_neg at hlt
  exact hn' ⟨hA, hn q ((hG.2 s).mem_toFinset.2 hlt)⟩

/-- **S5b(iii)**: monotone limit over the truncations `A_n ↑ g`. -/
theorem lim_bound (D : Data) (g : Finset (Fin D.M)) (c : Fin D.M) (N p : ℕ) (B : ENNReal)
    (hB : ∀ n, ∫⁻ ω, (∫⁻ s in Ico 0 (arrival ω (c, N)),
      ENNReal.ofReal (backlogA ω (An g n) s ^ p)) ∂D.P ≤ B) :
    ∫⁻ ω, (∫⁻ s in Ico 0 (arrival ω (c, N)),
      ENNReal.ofReal (backlogA ω (fun q : Job D.M => q.1 ∈ g) s ^ p)) ∂D.P ≤ B := by
  have hgood := CM4G.ae_good D
  have hψ : Measurable fun v : ℝ => ENNReal.ofReal (v ^ p) :=
    ENNReal.measurable_ofReal.comp (measurable_id.pow_const p)
  have hpt : ∀ᵐ ω ∂D.P, (∫⁻ s in Ico 0 (arrival ω (c, N)),
        ENNReal.ofReal (backlogA ω (fun q : Job D.M => q.1 ∈ g) s ^ p)) =
      ⨆ n, ∫⁻ s in Ico 0 (arrival ω (c, N)), ENNReal.ofReal (backlogA ω (An g n) s ^ p) := by
    filter_upwards [hgood] with ω hω
    have hG := hω.1
    have hmeas : ∀ n, Measurable fun s => ENNReal.ofReal (backlogA ω (An g n) s ^ p) := by
      intro n
      have : (fun s => ENNReal.ofReal (backlogA ω (An g n) s ^ p)) =
          fun s => ENNReal.ofReal (backlogM ω (An g n) s ^ p) := by
        funext s; rw [backlogM_eq hG]
      rw [this]
      exact hψ.comp (measurable_backlogM' _ (f := fun _ : ℝ => ω) measurable_const measurable_id)
    have hmono : Monotone fun n s => ENNReal.ofReal (backlogA ω (An g n) s ^ p) := by
      intro a b hab s
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (backlogA_nonneg ω _ s)
        (backlogA_mono hG (fun q hq => ⟨hq.1, lt_of_lt_of_le hq.2 hab⟩) s) p)
    rw [← lintegral_iSup hmeas hmono]
    refine lintegral_congr fun s => ?_
    obtain ⟨n, hn⟩ := trunc_lim hG g s
    refine le_antisymm ?_ (iSup_le fun m => ENNReal.ofReal_le_ofReal
      (pow_le_pow_left₀ (backlogA_nonneg ω _ s) (backlogA_mono hG (fun q hq => hq.1) s) p))
    rw [← hn]
    exact le_iSup (fun m => ENNReal.ofReal (backlogA ω (An g m) s ^ p)) n
  have hmono' : ∀ᵐ ω ∂D.P, Monotone fun n =>
      ∫⁻ s in Ico 0 (arrival ω (c, N)), ENNReal.ofReal (backlogA ω (An g n) s ^ p) := by
    filter_upwards [hgood] with ω hω
    intro a b hab
    exact lintegral_mono fun s => ENNReal.ofReal_le_ofReal (pow_le_pow_left₀
      (backlogA_nonneg ω _ s) (backlogA_mono hω.1 (fun q hq => ⟨hq.1, lt_of_lt_of_le hq.2 hab⟩) s) p)
  rw [lintegral_congr_ae hpt, lintegral_iSup' (f := fun n ω => ∫⁻ s in Ico 0 (arrival ω (c, N)),
    ENNReal.ofReal (backlogA ω (An g n) s ^ p)) (fun n => aem_full D _ c N _ hψ) hmono']
  exact iSup_le hB

/-- **S5b first moment, full class set**: `E∫_0^{T_{c,N}} V ≤ K(N+1)/(λ_c(1-ρ))` (finite). -/
theorem bound1_full (D : Data) (g : Finset (Fin D.M)) (c : Fin D.M) (hc : c ∈ g) (N : ℕ)
    (hρ : ∑ i ∈ g, D.lam i / D.mu i < 1) :
    ∫⁻ ω, (∫⁻ s in Ico 0 (arrival ω (c, N)),
        ENNReal.ofReal (backlogA ω (fun q : Job D.M => q.1 ∈ g) s ^ 1)) ∂D.P ≤
      ENNReal.ofReal ((∑ i ∈ g, D.lam i / D.mu i ^ 2) * ((N + 1) / D.lam c) /
        (1 - ∑ i ∈ g, D.lam i / D.mu i)) := by
  refine lim_bound D g c N 1 _ fun n => ?_
  have hS : ∀ q, An g n q → q ∈ g ×ˢ Finset.range n :=
    fun q hq => Finset.mem_product.2 ⟨hq.1, Finset.mem_range.2 hq.2⟩
  have h := s5_bound1 D g c hc N (An g n) (fun q hq => hq.1) _ hS
  have htop := (fin_trunc D _ hS c N 1 (by norm_num)).ne
  rw [← ENNReal.ofReal_toReal htop]
  exact ENNReal.ofReal_le_ofReal ((le_div_iff₀ (by linarith)).2 h)

end CM4S9

namespace CM4S10
open CoffmanMitrani MeasureTheory ProbabilityTheory Set CM4T CM4M CM4W CM4S1 CM4S3 CM4S4 CM4S5 CM4S6
  CM4S7 CM4S8 CM4S9

theorem inner_hat2 {r : ℝ} (hr : 0 < r) {M : ℕ} {ω : Omega M} (hG : FinGood ω)
    (A : Job M → Prop) (T : ℝ) :
    ∫⁻ s in Ico 0 T, ∫⁻ x, Gp 2 (backlogA ω A s) x ∂(expMeasure r) =
      ENNReal.ofReal (3 / r) * (∫⁻ s in Ico 0 T, ENNReal.ofReal (backlogA ω A s ^ 2)) +
        ENNReal.ofReal (6 / r ^ 2) * (∫⁻ s in Ico 0 T, ENNReal.ofReal (backlogA ω A s ^ 1)) +
        ENNReal.ofReal (6 / r ^ 3) * ENNReal.ofReal T := by
  have hV : Measurable fun s => backlogA ω A s := by
    have : (fun s => backlogA ω A s) = fun s => backlogM ω A s := by
      funext s; rw [backlogM_eq hG]
    rw [this]
    exact measurable_backlogM' _ (f := fun _ : ℝ => ω) measurable_const measurable_id
  have h : ∀ s, ∫⁻ x, Gp 2 (backlogA ω A s) x ∂(expMeasure r) =
      ENNReal.ofReal (3 / r) * ENNReal.ofReal (backlogA ω A s ^ 2) +
        ENNReal.ofReal (6 / r ^ 2) * ENNReal.ofReal (backlogA ω A s ^ 1) +
        ENNReal.ofReal (6 / r ^ 3) := by
    intro s
    have hv := backlogA_nonneg ω A s
    rw [Gp_two_hat hr hv, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1; ring
  simp_rw [h]
  rw [lintegral_add_right _ measurable_const,
    lintegral_add_left (show Measurable fun s => ENNReal.ofReal (3 / r) * ENNReal.ofReal (backlogA ω A s ^ 2) from
      (ENNReal.measurable_ofReal.comp (hV.pow_const 2)).const_mul _),
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    setLIntegral_const, Real.volume_Ico, sub_zero]

/-- **S5b(ii), second moment**, finite job set inside `g`:
`(1-ρ) E∫V² ≤ 2K E∫V + 2K₃ (N+1)/λ_c`. -/
theorem s5_bound2 (D : Data) (g : Finset (Fin D.M)) (c : Fin D.M) (hc : c ∈ g) (N : ℕ)
    (A : Job D.M → Prop) (hA : ∀ q, A q → q.1 ∈ g) (S : Finset (Job D.M))
    (hS : ∀ q, A q → q ∈ S) :
    (∫⁻ ω, (∫⁻ s in Ico 0 (arrival ω (c, N)), ENNReal.ofReal (backlogA ω A s ^ 2)) ∂D.P).toReal *
        (1 - ∑ i ∈ g, D.lam i / D.mu i) ≤
      2 * (∑ i ∈ g, D.lam i / D.mu i ^ 2) *
          (∫⁻ ω, (∫⁻ s in Ico 0 (arrival ω (c, N)), ENNReal.ofReal (backlogA ω A s ^ 1)) ∂D.P).toReal +
        2 * (∑ i ∈ g, D.lam i / D.mu i ^ 3) * ((N + 1) / D.lam c) := by
  have hgood := CM4G.ae_good D
  have hJ2top := (fin_trunc D S hS c N 2 le_rfl).ne
  have hJ1top := (fin_trunc D S hS c N 1 (by norm_num)).ne
  obtain ⟨j2, hj2, hJ2⟩ : ∃ j : ℝ, 0 ≤ j ∧
      (∫⁻ ω, (∫⁻ s in Ico 0 (arrival ω (c, N)), ENNReal.ofReal (backlogA ω A s ^ 2)) ∂D.P) =
        ENNReal.ofReal j :=
    ⟨_, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hJ2top).symm⟩
  obtain ⟨j1, hj1, hJ1⟩ : ∃ j : ℝ, 0 ≤ j ∧
      (∫⁻ ω, (∫⁻ s in Ico 0 (arrival ω (c, N)), ENNReal.ofReal (backlogA ω A s ^ 1)) ∂D.P) =
        ENNReal.ofReal j :=
    ⟨_, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hJ1top).symm⟩
  have hs4 := s4_le D g c hc N (p := 2) (by norm_num) A hA
  have hl := D.lam_pos c
  have hψ2 : Measurable fun v : ℝ => ENNReal.ofReal (v ^ 2) :=
    ENNReal.measurable_ofReal.comp (measurable_id.pow_const 2)
  have hψ1 : Measurable fun v : ℝ => ENNReal.ofReal (v ^ 1) :=
    ENNReal.measurable_ofReal.comp (measurable_id.pow_const 1)
  have hR : ∀ i ∈ g, ENNReal.ofReal (D.lam i) * ∫⁻ ω, (∫⁻ s in Ico 0 (arrival ω (c, N)),
        ∫⁻ x, Gp 2 (backlogA ω A s) x ∂(expMeasure (D.mu i))) ∂D.P =
      ENNReal.ofReal (D.lam i * (3 / D.mu i * j2 + 6 / D.mu i ^ 2 * j1 +
        6 / D.mu i ^ 3 * ((N + 1) / D.lam c))) := by
    intro i _
    have hmu := D.mu_pos i
    have hli := D.lam_pos i
    have h1 : ∀ᵐ ω ∂D.P, (∫⁻ s in Ico 0 (arrival ω (c, N)),
          ∫⁻ x, Gp 2 (backlogA ω A s) x ∂(expMeasure (D.mu i))) =
        ENNReal.ofReal (3 / D.mu i) *
            (∫⁻ s in Ico 0 (arrival ω (c, N)), ENNReal.ofReal (backlogA ω A s ^ 2)) +
          ENNReal.ofReal (6 / D.mu i ^ 2) *
            (∫⁻ s in Ico 0 (arrival ω (c, N)), ENNReal.ofReal (backlogA ω A s ^ 1)) +
          ENNReal.ofReal (6 / D.mu i ^ 3) * ENNReal.ofReal (arrival ω (c, N)) := by
      filter_upwards [hgood] with ω hω
      exact inner_hat2 hmu hω.1 A _
    have hTm : Measurable fun ω : Omega D.M => ENNReal.ofReal (arrival ω (c, N)) :=
      ENNReal.measurable_ofReal.comp (measurable_arrival _)
    rw [lintegral_congr_ae h1, lintegral_add_right _ (hTm.const_mul _),
      lintegral_add_left' ((aem_full D A c N _ hψ2).const_mul _),
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_const_mul _ hTm, ET_arr, hJ2, hJ1,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_mul hli.le]
  have hmain : ENNReal.ofReal 3 * ENNReal.ofReal j2 ≤
      ∑ i ∈ g, ENNReal.ofReal (D.lam i * (3 / D.mu i * j2 + 6 / D.mu i ^ 2 * j1 +
        6 / D.mu i ^ 3 * ((N + 1) / D.lam c))) := by
    refine le_trans ?_ (le_of_eq (Finset.sum_congr rfl hR))
    rw [← hJ2]
    refine le_trans ?_ hs4
    refine le_trans ?_ le_self_add
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun ω => le_trans ?_ le_add_self
    norm_num
  have hnn : ∀ i ∈ g, 0 ≤ D.lam i * (3 / D.mu i * j2 + 6 / D.mu i ^ 2 * j1 +
      6 / D.mu i ^ 3 * ((N + 1) / D.lam c)) := by
    intro i _
    have := D.lam_pos i
    have := D.mu_pos i
    positivity
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), ← ENNReal.ofReal_sum_of_nonneg hnn,
    ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg hnn)] at hmain
  rw [hJ2, ENNReal.toReal_ofReal hj2, hJ1, ENNReal.toReal_ofReal hj1]
  have e : ∑ i ∈ g, D.lam i * (3 / D.mu i * j2 + 6 / D.mu i ^ 2 * j1 +
      6 / D.mu i ^ 3 * ((N + 1) / D.lam c)) =
      3 * j2 * ∑ i ∈ g, D.lam i / D.mu i + 6 * j1 * ∑ i ∈ g, D.lam i / D.mu i ^ 2 +
        6 * (∑ i ∈ g, D.lam i / D.mu i ^ 3) * ((N + 1) / D.lam c) := by
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e] at hmain
  linear_combination (1 / 3 : ℝ) * hmain

/-- **S5b second moment, full class set** (finite). -/
theorem bound2_full (D : Data) (g : Finset (Fin D.M)) (c : Fin D.M) (hc : c ∈ g) (N : ℕ)
    (hρ : ∑ i ∈ g, D.lam i / D.mu i < 1) :
    ∫⁻ ω, (∫⁻ s in Ico 0 (arrival ω (c, N)),
        ENNReal.ofReal (backlogA ω (fun q : Job D.M => q.1 ∈ g) s ^ 2)) ∂D.P ≤
      ENNReal.ofReal ((2 * (∑ i ∈ g, D.lam i / D.mu i ^ 2) *
          ((∑ i ∈ g, D.lam i / D.mu i ^ 2) * ((N + 1) / D.lam c) /
            (1 - ∑ i ∈ g, D.lam i / D.mu i)) +
        2 * (∑ i ∈ g, D.lam i / D.mu i ^ 3) * ((N + 1) / D.lam c)) /
          (1 - ∑ i ∈ g, D.lam i / D.mu i)) := by
  refine lim_bound D g c N 2 _ fun n => ?_
  have hS : ∀ q, An g n q → q ∈ g ×ˢ Finset.range n :=
    fun q hq => Finset.mem_product.2 ⟨hq.1, Finset.mem_range.2 hq.2⟩
  have h2 := s5_bound2 D g c hc N (An g n) (fun q hq => hq.1) _ hS
  have h1 := s5_bound1 D g c hc N (An g n) (fun q hq => hq.1) _ hS
  have hK : 0 ≤ ∑ i ∈ g, D.lam i / D.mu i ^ 2 :=
    Finset.sum_nonneg fun i _ => div_nonneg (D.lam_pos i).le (pow_pos (D.mu_pos i) 2).le
  have h1' := (le_div_iff₀ (by linarith : (0 : ℝ) < 1 - ∑ i ∈ g, D.lam i / D.mu i)).2 h1
  have h3 := mul_le_mul_of_nonneg_left h1' (by linarith : (0 : ℝ) ≤ 2 * ∑ i ∈ g, D.lam i / D.mu i ^ 2)
  have htop := (fin_trunc D _ hS c N 2 le_rfl).ne
  rw [← ENNReal.ofReal_toReal htop]
  exact ENNReal.ofReal_le_ofReal ((le_div_iff₀ (by linarith)).2 (by linarith))

end CM4S10

namespace CM4S11
open CoffmanMitrani MeasureTheory ProbabilityTheory Set Filter CM4T CM4M CM4W CM4S1 CM4S3 CM4S4 CM4S5
  CM4S6 CM4S7 CM4S8 CM4S9 CM4S10

/-- **S6, real-analysis core.** -/
theorem s6_abstract (e q : ℕ → ℝ) (a b d K' C L : ℝ) (hq0 : ∀ n, 0 ≤ q n)
    (hid : ∀ N : ℕ, q N + a * ∑ m ∈ Finset.range (N + 1), e m + b * e N + d = K' * ((N : ℝ) + 1))
    (hsum : ∀ N : ℕ, ∑ m ∈ Finset.range (N + 1), q m ≤ C * ((N : ℝ) + 1))
    (he : Tendsto e atTop (nhds L)) : a * L = K' := by
  have hces : Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹ * ∑ m ∈ Finset.range (N + 1), e m)
      atTop (nhds L) := by
    have := he.cesaro.comp (tendsto_add_atTop_nat 1)
    refine this.congr fun N => ?_
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
  have hinv : Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.congr fun N => one_div _
  have hq : Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹ * q N) atTop (nhds (K' - a * L)) := by
    have h := ((tendsto_const_nhds (x := K')).sub (hces.const_mul a)).sub
      (((hinv.mul he).const_mul b).add (hinv.const_mul d))
    rw [show K' - a * L - (b * (0 * L) + d * 0) = K' - a * L by ring] at h
    refine h.congr fun N => ?_
    have hqN : q N = K' * ((N : ℝ) + 1) - a * ∑ m ∈ Finset.range (N + 1), e m - b * e N - d := by
      linarith [hid N]
    have hN : ((N : ℝ) + 1) ≠ 0 := by positivity
    rw [hqN]
    field_simp
    ring
  have hge : 0 ≤ K' - a * L :=
    ge_of_tendsto hq (Eventually.of_forall fun N =>
      mul_nonneg (inv_nonneg.2 (by positivity)) (hq0 N))
  have hle : K' - a * L ≤ 0 := by
    by_contra hpos
    push_neg at hpos
    set δ := K' - a * L with hδ
    have hC : 0 ≤ C := by
      have h0 := hsum 0
      simp only [Finset.sum_range_one, Nat.cast_zero, zero_add, mul_one] at h0
      exact le_trans (hq0 0) h0
    obtain ⟨N0, hN0⟩ := eventually_atTop.1 (hq.eventually (lt_mem_nhds (half_lt_self hpos)))
    obtain ⟨N1, hN1⟩ := exists_nat_gt (4 * C / δ)
    set N := max N0 N1 with hNdef
    have hlow : ∀ m, N ≤ m → δ / 2 * ((N : ℝ) + 1) ≤ q m := by
      intro m hm
      have h1 := hN0 m (le_trans (le_max_left _ _) hm)
      have hm' : (N : ℝ) ≤ m := by exact_mod_cast hm
      have hpos' : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      rw [inv_mul_eq_div, lt_div_iff₀ hpos'] at h1
      nlinarith
    have hsub : ∑ m ∈ Finset.Ico N (2 * N + 1), q m ≤ ∑ m ∈ Finset.range (2 * N + 1), q m :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (fun m hm => by
          simp only [Finset.mem_Ico, Finset.mem_range] at hm ⊢
          omega)
        (fun m _ _ => hq0 m)
    have hcard : ∑ _m ∈ Finset.Ico N (2 * N + 1), δ / 2 * ((N : ℝ) + 1) ≤
        ∑ m ∈ Finset.Ico N (2 * N + 1), q m :=
      Finset.sum_le_sum fun m hm => hlow m (Finset.mem_Ico.1 hm).1
    have hc : 2 * N + 1 - N = N + 1 := by omega
    rw [Finset.sum_const, Nat.card_Ico, hc, nsmul_eq_mul] at hcard
    have hs := hsum (2 * N)
    push_cast at hcard hs
    have hN1' : 4 * C / δ < (N : ℝ) + 1 := by
      have : (N1 : ℝ) ≤ N := by exact_mod_cast le_max_right N0 N1
      linarith
    rw [div_lt_iff₀ hpos] at hN1'
    have hNp : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have := mul_lt_mul_of_pos_left hN1' hNp
    nlinarith
  linarith

/-- The class-`c` arrival-epoch backlog is a.e.-measurable. -/
theorem b_aem (D : Data) (A : Job D.M → Prop) (c : Fin D.M) (N : ℕ) :
    AEMeasurable (fun ω => backlogA ω A (arrival ω (c, N))) D.P := by
  have hgood := CM4G.ae_good D
  refine (measurable_backlogM' A (f := fun ω : Omega D.M => ω) measurable_id
    (measurable_arrival (c, N))).aemeasurable.congr ?_
  filter_upwards [hgood] with ω hω
  exact backlogM_eq hω.1 _ _

theorem e_toReal (D : Data) (A : Job D.M → Prop) (c : Fin D.M) (N : ℕ) :
    ∫ ω, backlogA ω A (arrival ω (c, N)) ∂D.P =
      (∫⁻ ω, ENNReal.ofReal (backlogA ω A (arrival ω (c, N)) ^ 1) ∂D.P).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun ω => backlogA_nonneg _ _ _)
    (b_aem D A c N).aestronglyMeasurable]
  simp only [pow_one]

end CM4S11

namespace CM4S12
open CoffmanMitrani MeasureTheory ProbabilityTheory Set Filter CM4T CM4M CM4W CM4S1 CM4S3 CM4S4 CM4S5
  CM4S6 CM4S7 CM4S8 CM4S9 CM4S10 CM4S11

theorem term_le (D : Data) (A : Job D.M → Prop) (c : Fin D.M) (N : ℕ) (ψ : ℝ → ENNReal)
    (hψ : Measurable ψ) :
    ∫⁻ ω, ψ (backlogA ω A (arrival ω (c, N))) ∂D.P ≤
      ENNReal.ofReal (D.lam c) * ∫⁻ ω, (∫⁻ s in Ico 0 (arrival ω (c, N)), ψ (backlogA ω A s)) ∂D.P := by
  rw [← asta_sum D A c N ψ hψ]
  exact Finset.single_le_sum (f := fun m => ∫⁻ ω, ψ (backlogA ω A (arrival ω (c, m))) ∂D.P)
    (fun _ _ => bot_le) (Finset.self_mem_range_succ N)

theorem fin_full (D : Data) (g : Finset (Fin D.M)) (c : Fin D.M) (hc : c ∈ g) (N : ℕ)
    (hρ : ∑ i ∈ g, D.lam i / D.mu i < 1) {p : ℕ} (hp1 : 1 ≤ p) (hp : p ≤ 2) :
    ∫⁻ ω, (∫⁻ s in Ico 0 (arrival ω (c, N)),
        ENNReal.ofReal (backlogA ω (fun q : Job D.M => q.1 ∈ g) s ^ p)) ∂D.P < ⊤ := by
  interval_cases p
  · exact lt_of_le_of_lt (bound1_full D g c hc N hρ) ENNReal.ofReal_lt_top
  · exact lt_of_le_of_lt (bound2_full D g c hc N hρ) ENNReal.ofReal_lt_top

theorem fin_pt (D : Data) (g : Finset (Fin D.M)) (c : Fin D.M) (hc : c ∈ g) (N : ℕ)
    (hρ : ∑ i ∈ g, D.lam i / D.mu i < 1) {p : ℕ} (hp1 : 1 ≤ p) (hp : p ≤ 2) (m : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (backlogA ω (fun q : Job D.M => q.1 ∈ g) (arrival ω (c, m)) ^ p) ∂D.P
      < ⊤ := by
  have hψ : Measurable fun v : ℝ => ENNReal.ofReal (v ^ p) :=
    ENNReal.measurable_ofReal.comp (measurable_id.pow_const p)
  exact lt_of_le_of_lt (term_le D _ c m _ hψ)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (fin_full D g c hc m hρ hp1 hp))

/-- **S6 identity (real form)** of `s4_identity`. -/
theorem s6_identity (D : Data) (g : Finset (Fin D.M)) (c : Fin D.M) (hc : c ∈ g) (N : ℕ)
    (hρ : ∑ i ∈ g, D.lam i / D.mu i < 1) :
    (∫⁻ ω, ENNReal.ofReal (backlogA ω (fun q : Job D.M => q.1 ∈ g) (arrival ω (c, N)) ^ 2)
        ∂D.P).toReal +
      2 * (∫⁻ ω, (∫⁻ s in Ico 0 (arrival ω (c, N)),
        ENNReal.ofReal (backlogA ω (fun q : Job D.M => q.1 ∈ g) s ^ 1)) ∂D.P).toReal +
      (2 / D.mu c * (∫⁻ ω, ENNReal.ofReal
        (backlogA ω (fun q : Job D.M => q.1 ∈ g) (arrival ω (c, N)) ^ 1) ∂D.P).toReal +
        2 / D.mu c ^ 2) =
      ∑ i ∈ g, D.lam i * (2 / D.mu i * (∫⁻ ω, (∫⁻ s in Ico 0 (arrival ω (c, N)),
        ENNReal.ofReal (backlogA ω (fun q : Job D.M => q.1 ∈ g) s ^ 1)) ∂D.P).toReal +
        2 / D.mu i ^ 2 * ((N + 1) / D.lam c)) := by
  haveI := CM4W.P_isProb D
  have hgood := CM4G.ae_good D
  obtain ⟨q, hq0, hQ⟩ : ∃ x : ℝ, 0 ≤ x ∧
      (∫⁻ ω, ENNReal.ofReal (backlogA ω (fun q : Job D.M => q.1 ∈ g) (arrival ω (c, N)) ^ 2)
        ∂D.P) = ENNReal.ofReal x :=
    ⟨_, ENNReal.toReal_nonneg,
      (ENNReal.ofReal_toReal (fin_pt D g c hc N hρ (p := 2) (by norm_num) le_rfl N).ne).symm⟩
  obtain ⟨e1, he0, hE⟩ : ∃ x : ℝ, 0 ≤ x ∧
      (∫⁻ ω, ENNReal.ofReal (backlogA ω (fun q : Job D.M => q.1 ∈ g) (arrival ω (c, N)) ^ 1)
        ∂D.P) = ENNReal.ofReal x :=
    ⟨_, ENNReal.toReal_nonneg,
      (ENNReal.ofReal_toReal (fin_pt D g c hc N hρ (p := 1) le_rfl (by norm_num) N).ne).symm⟩
  obtain ⟨j, hj0, hI⟩ : ∃ x : ℝ, 0 ≤ x ∧
      (∫⁻ ω, (∫⁻ s in Ico 0 (arrival ω (c, N)),
        ENNReal.ofReal (backlogA ω (fun q : Job D.M => q.1 ∈ g) s ^ 1)) ∂D.P) = ENNReal.ofReal x :=
    ⟨_, ENNReal.toReal_nonneg,
      (ENNReal.ofReal_toReal (fin_full D g c hc N hρ (p := 1) le_rfl (by norm_num)).ne).symm⟩
  rw [hQ, hE, hI, ENNReal.toReal_ofReal hq0, ENNReal.toReal_ofReal he0, ENNReal.toReal_ofReal hj0]
  have hs4 := s4_identity D g c hc N
  have hmc := D.mu_pos c
  have hl := D.lam_pos c
  have hQaem : AEMeasurable (fun ω => ENNReal.ofReal
      (backlogA ω (fun q : Job D.M => q.1 ∈ g) (arrival ω (c, N)) ^ 2)) D.P :=
    ENNReal.measurable_ofReal.comp_aemeasurable ((b_aem D _ c N).pow_const 2)
  have hI0 : (∫⁻ ω, (2 * ∫⁻ s in Ico 0 (arrival ω (c, N)),
      ENNReal.ofReal (backlogA ω (fun q : Job D.M => q.1 ∈ g) s)) ∂D.P) =
      ENNReal.ofReal 2 * ENNReal.ofReal j := by
    rw [← hI]
    simp only [pow_one]
    rw [lintegral_const_mul' _ _ (by norm_num)]
    norm_num
  have hB : (∫⁻ ω, ∫⁻ x, G2 (backlogA ω (fun q : Job D.M => q.1 ∈ g) (arrival ω (c, N))) x
      ∂(expMeasure (D.mu c)) ∂D.P) =
      ENNReal.ofReal (2 / D.mu c) * ENNReal.ofReal e1 + ENNReal.ofReal (2 / D.mu c ^ 2) := by
    have pt : ∀ ω : Omega D.M, ∫⁻ x, G2 (backlogA ω (fun q : Job D.M => q.1 ∈ g)
        (arrival ω (c, N))) x ∂(expMeasure (D.mu c)) =
        ENNReal.ofReal (2 / D.mu c) * ENNReal.ofReal
          (backlogA ω (fun q : Job D.M => q.1 ∈ g) (arrival ω (c, N)) ^ 1) +
          ENNReal.ofReal (2 / D.mu c ^ 2) := by
      intro ω
      have hv := backlogA_nonneg ω (fun q : Job D.M => q.1 ∈ g) (arrival ω (c, N))
      simp_rw [G2_eq_Gp]
      rw [Gp_one_hat hmc hv, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1; ring
    rw [lintegral_congr pt, lintegral_add_right _ measurable_const,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const, measure_univ, mul_one, hE]
  have hR : ∀ i ∈ g, ENNReal.ofReal (D.lam i) * ∫⁻ ω, (∫⁻ s in Ico 0 (arrival ω (c, N)),
        ∫⁻ x, G2 (backlogA ω (fun q : Job D.M => q.1 ∈ g) s) x ∂(expMeasure (D.mu i))) ∂D.P =
      ENNReal.ofReal (D.lam i * (2 / D.mu i * j + 2 / D.mu i ^ 2 * ((N + 1) / D.lam c))) := by
    intro i _
    have hmu := D.mu_pos i
    have hli := D.lam_pos i
    simp_rw [G2_eq_Gp]
    have h1 : ∀ ω : Omega D.M, (∫⁻ s in Ico 0 (arrival ω (c, N)),
          ∫⁻ x, Gp 1 (backlogA ω (fun q : Job D.M => q.1 ∈ g) s) x ∂(expMeasure (D.mu i))) =
        ENNReal.ofReal (2 / D.mu i) *
            (∫⁻ s in Ico 0 (arrival ω (c, N)),
              ENNReal.ofReal (backlogA ω (fun q : Job D.M => q.1 ∈ g) s ^ 1)) +
          ENNReal.ofReal (2 / D.mu i ^ 2) * ENNReal.ofReal (arrival ω (c, N)) :=
      fun ω => inner_hat1 hmu ω _ _
    have hTm : Measurable fun ω : Omega D.M => ENNReal.ofReal (arrival ω (c, N)) :=
      ENNReal.measurable_ofReal.comp (measurable_arrival _)
    rw [lintegral_congr fun ω => h1 ω, lintegral_add_right _ (hTm.const_mul _),
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul _ hTm, ET_arr, hI,
      ENNReal.ofReal_mul hli.le, ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
  have hnn : ∀ i ∈ g, 0 ≤ D.lam i * (2 / D.mu i * j + 2 / D.mu i ^ 2 * ((N + 1) / D.lam c)) := by
    intro i _
    have := D.lam_pos i
    have := D.mu_pos i
    positivity
  rw [lintegral_add_left' hQaem, hI0, hB, hQ, Finset.sum_congr rfl hR,
    ← ENNReal.ofReal_sum_of_nonneg hnn,
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_eq_ofReal_iff (by positivity) (Finset.sum_nonneg hnn)] at hs4
  exact hs4

/-- Second-moment Cesàro bound `Σ_{m≤N} E b_m² ≤ C (N+1)`. -/
theorem s6_sum (D : Data) (g : Finset (Fin D.M)) (c : Fin D.M) (hc : c ∈ g)
    (hρ : ∑ i ∈ g, D.lam i / D.mu i < 1) (N : ℕ) :
    ∑ m ∈ Finset.range (N + 1), (∫⁻ ω, ENNReal.ofReal
        (backlogA ω (fun q : Job D.M => q.1 ∈ g) (arrival ω (c, m)) ^ 2) ∂D.P).toReal ≤
      D.lam c * ((2 * (∑ i ∈ g, D.lam i / D.mu i ^ 2) *
          ((∑ i ∈ g, D.lam i / D.mu i ^ 2) / D.lam c / (1 - ∑ i ∈ g, D.lam i / D.mu i)) +
        2 * (∑ i ∈ g, D.lam i / D.mu i ^ 3) / D.lam c) /
          (1 - ∑ i ∈ g, D.lam i / D.mu i)) * ((N : ℝ) + 1) := by
  have hl := D.lam_pos c
  have hψ : Measurable fun v : ℝ => ENNReal.ofReal (v ^ 2) :=
    ENNReal.measurable_ofReal.comp (measurable_id.pow_const 2)
  have h := asta_sum D (fun q : Job D.M => q.1 ∈ g) c N _ hψ
  have hfin : ∀ m ∈ Finset.range (N + 1), (∫⁻ ω, ENNReal.ofReal
      (backlogA ω (fun q : Job D.M => q.1 ∈ g) (arrival ω (c, m)) ^ 2) ∂D.P) ≠ ⊤ :=
    fun m _ => (fin_pt D g c hc N hρ (p := 2) (by norm_num) le_rfl m).ne
  rw [← ENNReal.toReal_sum hfin, h, ENNReal.toReal_mul, ENNReal.toReal_ofReal hl.le]
  have hB := bound2_full D g c hc N hρ
  have hne : (1 - ∑ i ∈ g, D.lam i / D.mu i) ≠ 0 := by linarith
  have hK : 0 ≤ ∑ i ∈ g, D.lam i / D.mu i ^ 2 :=
    Finset.sum_nonneg fun i _ => div_nonneg (D.lam_pos i).le (pow_pos (D.mu_pos i) 2).le
  have hK3 : 0 ≤ ∑ i ∈ g, D.lam i / D.mu i ^ 3 :=
    Finset.sum_nonneg fun i _ => div_nonneg (D.lam_pos i).le (pow_pos (D.mu_pos i) 3).le
  have hpos : 0 < 1 - ∑ i ∈ g, D.lam i / D.mu i := by linarith
  have hB' := ENNReal.toReal_le_of_le_ofReal (by positivity) hB
  have heq : (2 * (∑ i ∈ g, D.lam i / D.mu i ^ 2) *
          ((∑ i ∈ g, D.lam i / D.mu i ^ 2) * ((N + 1) / D.lam c) /
            (1 - ∑ i ∈ g, D.lam i / D.mu i)) +
        2 * (∑ i ∈ g, D.lam i / D.mu i ^ 3) * ((N + 1) / D.lam c)) /
          (1 - ∑ i ∈ g, D.lam i / D.mu i) =
      ((2 * (∑ i ∈ g, D.lam i / D.mu i ^ 2) *
          ((∑ i ∈ g, D.lam i / D.mu i ^ 2) / D.lam c / (1 - ∑ i ∈ g, D.lam i / D.mu i)) +
        2 * (∑ i ∈ g, D.lam i / D.mu i ^ 3) / D.lam c) /
          (1 - ∑ i ∈ g, D.lam i / D.mu i)) * ((N : ℝ) + 1) := by
    field_simp
  rw [heq] at hB'
  calc D.lam c * _ ≤ D.lam c * (((2 * (∑ i ∈ g, D.lam i / D.mu i ^ 2) *
          ((∑ i ∈ g, D.lam i / D.mu i ^ 2) / D.lam c / (1 - ∑ i ∈ g, D.lam i / D.mu i)) +
        2 * (∑ i ∈ g, D.lam i / D.mu i ^ 3) / D.lam c) /
          (1 - ∑ i ∈ g, D.lam i / D.mu i)) * ((N : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hB' hl.le
    _ = _ := by ring

/-- **C3' for one chain**: if `E b_n → L` then `L = K/(1-ρ)`. -/
theorem C3_limit (D : Data) (g : Finset (Fin D.M)) (c : Fin D.M) (hc : c ∈ g)
    (hρ : ∑ i ∈ g, D.lam i / D.mu i < 1) (L : ℝ)
    (hL : Tendsto (fun n : ℕ => ∫ ω, backlogA ω (fun q : Job D.M => q.1 ∈ g) (arrival ω (c, n)) ∂D.P)
      atTop (nhds L)) :
    L = (∑ i ∈ g, D.lam i / D.mu i ^ 2) / (1 - ∑ i ∈ g, D.lam i / D.mu i) := by
  have hl := D.lam_pos c
  have hmc := D.mu_pos c
  have hpos : 0 < 1 - ∑ i ∈ g, D.lam i / D.mu i := by linarith
  have hψ : Measurable fun v : ℝ => ENNReal.ofReal (v ^ 1) :=
    ENNReal.measurable_ofReal.comp (measurable_id.pow_const 1)
  have hid : ∀ N : ℕ,
      (∫⁻ ω, ENNReal.ofReal (backlogA ω (fun q : Job D.M => q.1 ∈ g) (arrival ω (c, N)) ^ 2)
        ∂D.P).toReal +
      2 * (1 - ∑ i ∈ g, D.lam i / D.mu i) / D.lam c *
        ∑ m ∈ Finset.range (N + 1),
          ∫ ω, backlogA ω (fun q : Job D.M => q.1 ∈ g) (arrival ω (c, m)) ∂D.P +
      2 / D.mu c * ∫ ω, backlogA ω (fun q : Job D.M => q.1 ∈ g) (arrival ω (c, N)) ∂D.P +
      2 / D.mu c ^ 2 =
      2 * (∑ i ∈ g, D.lam i / D.mu i ^ 2) / D.lam c * ((N : ℝ) + 1) := by
    intro N
    have hS := asta_sum D (fun q : Job D.M => q.1 ∈ g) c N _ hψ
    have hfin : ∀ m ∈ Finset.range (N + 1), (∫⁻ ω, ENNReal.ofReal
        (backlogA ω (fun q : Job D.M => q.1 ∈ g) (arrival ω (c, m)) ^ 1) ∂D.P) ≠ ⊤ :=
      fun m _ => (fin_pt D g c hc N hρ (p := 1) le_rfl (by norm_num) m).ne
    have hS' := congrArg ENNReal.toReal hS
    rw [ENNReal.toReal_sum hfin, ENNReal.toReal_mul, ENNReal.toReal_ofReal hl.le] at hS'
    simp_rw [e_toReal]
    rw [hS']
    have hid0 := s6_identity D g c hc N hρ
    set j := (∫⁻ ω, (∫⁻ s in Ico 0 (arrival ω (c, N)),
        ENNReal.ofReal (backlogA ω (fun q : Job D.M => q.1 ∈ g) s ^ 1)) ∂D.P).toReal
    have e : ∑ i ∈ g, D.lam i * (2 / D.mu i * j + 2 / D.mu i ^ 2 * ((N + 1) / D.lam c)) =
        2 * j * ∑ i ∈ g, D.lam i / D.mu i +
          2 * (∑ i ∈ g, D.lam i / D.mu i ^ 2) * ((N + 1) / D.lam c) := by
      simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [e] at hid0
    have h1 : 2 * (1 - ∑ i ∈ g, D.lam i / D.mu i) / D.lam c * (D.lam c * j) =
        2 * (1 - ∑ i ∈ g, D.lam i / D.mu i) * j := by
      field_simp
    have h2 : 2 * (∑ i ∈ g, D.lam i / D.mu i ^ 2) / D.lam c * ((N : ℝ) + 1) =
        2 * (∑ i ∈ g, D.lam i / D.mu i ^ 2) * ((N + 1) / D.lam c) := by ring
    rw [h1, h2]
    linarith
  have key := s6_abstract _ _ _ _ _ _ _ L (fun n => ENNReal.toReal_nonneg) hid
    (s6_sum D g c hc hρ) hL
  have hl' := hl.ne'
  field_simp at key
  rw [eq_div_iff hpos.ne']
  linarith

end CM4S12


set_option autoImplicit false


/-! C1 foundations for 608dae3b (CoffmanMitrani.chain_solution), DECOMPOSE v2 child C1.
C1a: almost-sure positivity of interarrival and service times (from the exponential marginals).
C1b: measure-free calculus of `served` (outer measure only; no measurability of `S` is assumed). -/

namespace CM4
open CoffmanMitrani MeasureTheory ProbabilityTheory

/-! ### C1b: `served` calculus -/

theorem served_vol_ne_top {M : ℕ} (S : Schedule M) (j : Job M) (ω : Omega M) (t : ℝ) :
    volume ({s : ℝ | S ω s = some j} ∩ Set.Ico 0 t) ≠ ⊤ :=
  ((measure_mono Set.inter_subset_right).trans_lt measure_Ico_lt_top).ne

theorem served_nonneg {M : ℕ} (S : Schedule M) (j : Job M) (ω : Omega M) (t : ℝ) :
    0 ≤ served S j ω t := ENNReal.toReal_nonneg

theorem served_of_nonpos {M : ℕ} (S : Schedule M) (j : Job M) (ω : Omega M) {t : ℝ}
    (ht : t ≤ 0) : served S j ω t = 0 := by
  unfold served
  rw [Set.Ico_eq_empty (not_lt.2 ht), Set.inter_empty, measure_empty, ENNReal.toReal_zero]

theorem served_mono {M : ℕ} (S : Schedule M) (j : Job M) (ω : Omega M) {t t' : ℝ}
    (h : t ≤ t') : served S j ω t ≤ served S j ω t' :=
  ENNReal.toReal_mono (served_vol_ne_top S j ω t')
    (measure_mono (Set.inter_subset_inter_right _ (Set.Ico_subset_Ico_right h)))

theorem served_le_add {M : ℕ} (S : Schedule M) (j : Job M) (ω : Omega M) {t t' : ℝ}
    (h : t ≤ t') : served S j ω t' ≤ served S j ω t + (t' - t) := by
  have hsub : {s : ℝ | S ω s = some j} ∩ Set.Ico 0 t' ⊆
      ({s : ℝ | S ω s = some j} ∩ Set.Ico 0 t) ∪ Set.Ico t t' := by
    intro s ⟨hs1, hs2⟩
    by_cases hst : s < t
    · exact Or.inl ⟨hs1, hs2.1, hst⟩
    · exact Or.inr ⟨not_lt.1 hst, hs2.2⟩
  have hle : volume ({s : ℝ | S ω s = some j} ∩ Set.Ico 0 t') ≤
      ENNReal.ofReal (served S j ω t + (t' - t)) := by
    calc volume ({s : ℝ | S ω s = some j} ∩ Set.Ico 0 t')
        ≤ volume ({s : ℝ | S ω s = some j} ∩ Set.Ico 0 t) + volume (Set.Ico t t') :=
          (measure_mono hsub).trans (measure_union_le _ _)
      _ = ENNReal.ofReal (served S j ω t + (t' - t)) := by
          rw [Real.volume_Ico, ENNReal.ofReal_add (served_nonneg S j ω t) (by linarith)]
          unfold served
          rw [ENNReal.ofReal_toReal (served_vol_ne_top S j ω t)]
  exact ENNReal.toReal_le_of_le_ofReal (add_nonneg (served_nonneg S j ω t) (by linarith)) hle

theorem served_serving {M : ℕ} (S : Schedule M) (j : Job M) (ω : Omega M) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hS : ∀ s ∈ Set.Ico a b, S ω s = some j) :
    served S j ω b = served S j ω a + (b - a) := by
  have hset : {s : ℝ | S ω s = some j} ∩ Set.Ico 0 b =
      ({s : ℝ | S ω s = some j} ∩ Set.Ico 0 a) ∪ Set.Ico a b := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Ico, Set.mem_union]
    constructor
    · rintro ⟨h1, h2, h3⟩
      by_cases hsa : s < a
      · exact Or.inl ⟨h1, h2, hsa⟩
      · exact Or.inr ⟨not_lt.1 hsa, h3⟩
    · rintro (⟨h1, h2, h3⟩ | ⟨h2, h3⟩)
      · exact ⟨h1, h2, lt_of_lt_of_le h3 hab⟩
      · exact ⟨hS s ⟨h2, h3⟩, le_trans ha h2, h3⟩
  have hdisj : Disjoint ({s : ℝ | S ω s = some j} ∩ Set.Ico 0 a) (Set.Ico a b) := by
    rw [Set.disjoint_left]
    intro s hs1 hs2
    exact absurd hs2.1 (not_le.2 hs1.2.2)
  unfold served
  rw [hset, measure_union hdisj measurableSet_Ico, Real.volume_Ico,
    ENNReal.toReal_add (served_vol_ne_top S j ω a) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by linarith)]

theorem served_idle {M : ℕ} (S : Schedule M) (j : Job M) (ω : Omega M) {a b : ℝ}
    (hab : a ≤ b) (hS : ∀ s ∈ Set.Ico a b, S ω s ≠ some j) :
    served S j ω b = served S j ω a := by
  have hset : {s : ℝ | S ω s = some j} ∩ Set.Ico 0 b =
      {s : ℝ | S ω s = some j} ∩ Set.Ico 0 a := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Ico]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, ?_⟩
      by_contra hsa
      exact hS s ⟨not_lt.1 hsa, h3⟩ h1
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, lt_of_lt_of_le h3 hab⟩
  unfold served
  rw [hset]

/-- `served` is 1-Lipschitz and monotone, hence continuous in `t`. -/
theorem served_continuous {M : ℕ} (S : Schedule M) (j : Job M) (ω : Omega M) :
    Continuous (served S j ω) := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun t t' => ?_).continuous
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul]
  rcases le_total t t' with h | h
  · have h1 := served_mono S j ω h
    have h2 := served_le_add S j ω h
    rw [abs_sub_comm (served S j ω t), abs_sub_comm t, abs_of_nonneg (sub_nonneg.2 h1),
      abs_of_nonneg (sub_nonneg.2 h)]
    linarith
  · have h1 := served_mono S j ω h
    have h2 := served_le_add S j ω h
    rw [abs_of_nonneg (sub_nonneg.2 h1), abs_of_nonneg (sub_nonneg.2 h)]
    linarith

/-! ### C1a: almost-sure positivity -/

theorem expMeasure_ae_pos {r : ℝ} (hr : 0 < r) : ∀ᵐ x ∂(expMeasure r), 0 < x := by
  haveI := isProbabilityMeasure_expMeasure hr
  rw [ae_iff]
  have hset : {x : ℝ | ¬ 0 < x} = Set.Iic 0 := by ext x; simp
  rw [hset, ← ofReal_cdf, cdf_expMeasure_eq hr]
  simp

theorem ae_interarrival_pos (D : Data) : ∀ᵐ ω ∂D.P, ∀ j : Job D.M, 0 < ω.1 j := by
  rw [ae_all_iff]
  intro j
  haveI : ∀ j : Job D.M, IsProbabilityMeasure (expMeasure (D.lam j.1)) :=
    fun j => isProbabilityMeasure_expMeasure (D.lam_pos j.1)
  haveI : ∀ j : Job D.M, IsProbabilityMeasure (expMeasure (D.mu j.1)) :=
    fun j => isProbabilityMeasure_expMeasure (D.mu_pos j.1)
  have hmeas : Measurable fun ω : Omega D.M => ω.1 j :=
    (measurable_pi_apply j).comp measurable_fst
  have hmap : D.P.map (fun ω : Omega D.M => ω.1 j) = expMeasure (D.lam j.1) := by
    have : (fun ω : Omega D.M => ω.1 j) = (fun x : Job D.M → ℝ => x j) ∘ Prod.fst := rfl
    rw [this, ← Measure.map_map (measurable_pi_apply j) measurable_fst]
    unfold Data.P
    rw [Measure.map_fst_prod, measure_univ, one_smul, Measure.infinitePi_map_eval]
  have h := expMeasure_ae_pos (D.lam_pos j.1)
  rw [← hmap] at h
  exact ae_of_ae_map hmeas.aemeasurable h

theorem ae_service_pos (D : Data) : ∀ᵐ ω ∂D.P, ∀ j : Job D.M, 0 < ω.2.1 j := by
  rw [ae_all_iff]
  intro j
  haveI : ∀ j : Job D.M, IsProbabilityMeasure (expMeasure (D.lam j.1)) :=
    fun j => isProbabilityMeasure_expMeasure (D.lam_pos j.1)
  haveI : ∀ j : Job D.M, IsProbabilityMeasure (expMeasure (D.mu j.1)) :=
    fun j => isProbabilityMeasure_expMeasure (D.mu_pos j.1)
  have hmeas : Measurable fun ω : Omega D.M => ω.2.1 j :=
    (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)
  have hmap : D.P.map (fun ω : Omega D.M => ω.2.1 j) = expMeasure (D.mu j.1) := by
    have : (fun ω : Omega D.M => ω.2.1 j) =
        (fun x : Job D.M → ℝ => x j) ∘ Prod.fst ∘ Prod.snd := rfl
    rw [this, ← Measure.map_map (measurable_pi_apply j) (measurable_fst.comp measurable_snd),
      ← Measure.map_map measurable_fst measurable_snd]
    unfold Data.P
    rw [Measure.map_snd_prod, measure_univ, one_smul, Measure.map_fst_prod, measure_univ,
      one_smul, Measure.infinitePi_map_eval]
  have h := expMeasure_ae_pos (D.mu_pos j.1)
  rw [← hmap] at h
  exact ae_of_ae_map hmeas.aemeasurable h

/-! ### C1c: right-local constancy of a priority schedule and busy-time accounting -/

open Filter Topology

/-- The pointwise priority clause of `IsPriority` at a sample point. -/
def PrioAt {M : ℕ} (σ : Equiv.Perm (Fin M)) (S : Schedule M) (ω : Omega M) : Prop :=
  ∀ (t : ℝ) (j j' : Job M), S ω t = some j → present S j' ω t →
    σ.symm j.1 < σ.symm j'.1 ∨ (j.1 = j'.1 ∧ j.2 ≤ j'.2)

/-- Finitely many arrivals in bounded time, plus `PathStrategy` clauses 2 and 3 at `ω`. -/
def GoodAt {M : ℕ} (S : Schedule M) (ω : Omega M) : Prop :=
  (∀ T : ℝ, Set.Finite {j : Job M | arrival ω j ≤ T}) ∧
  (∀ (t : ℝ) (j : Job M), S ω t = some j → present S j ω t) ∧
  (∀ t : ℝ, S ω t = none ↔ ∀ j : Job M, ¬ present S j ω t)

theorem prio_antisymm {M : ℕ} (σ : Equiv.Perm (Fin M)) (j j' : Job M)
    (h1 : σ.symm j.1 < σ.symm j'.1 ∨ (j.1 = j'.1 ∧ j.2 ≤ j'.2))
    (h2 : σ.symm j'.1 < σ.symm j.1 ∨ (j'.1 = j.1 ∧ j'.2 ≤ j.2)) : j = j' := by
  rcases h1 with h1 | ⟨h1a, h1b⟩ <;> rcases h2 with h2 | ⟨h2a, h2b⟩
  · exact absurd (h1.trans h2) (lt_irrefl _)
  · rw [h2a] at h1; exact absurd h1 (lt_irrefl _)
  · rw [h1a] at h2; exact absurd h2 (lt_irrefl _)
  · exact Prod.ext h1a (le_antisymm h1b h2b)

theorem sched_eq_of_present_iff {M : ℕ} (σ : Equiv.Perm (Fin M)) (S : Schedule M)
    (ω : Omega M) (hG : GoodAt S ω) (hP : PrioAt σ S ω) {t T : ℝ}
    (hiff : ∀ j, present S j ω t ↔ present S j ω T) : S ω t = S ω T := by
  obtain ⟨_, hpres, hidle⟩ := hG
  cases hT : S ω T with
  | none =>
    rw [hidle] at hT ⊢
    intro j hj; exact hT j ((hiff j).1 hj)
  | some j =>
    have hjT := hpres T j hT
    cases ht : S ω t with
    | none =>
      rw [hidle] at ht; exact absurd ((hiff j).2 hjT) (ht j)
    | some j' =>
      have hj't := hpres t j' ht
      have h1 := hP T j j' hT ((hiff j').1 hj't)
      have h2 := hP t j' j ht ((hiff j).2 hjT)
      rw [prio_antisymm σ j j' h1 h2]

/-- A priority schedule is right-locally constant at every time. -/
theorem right_const {M : ℕ} (σ : Equiv.Perm (Fin M)) (S : Schedule M) (ω : Omega M)
    (hG : GoodAt S ω) (hP : PrioAt σ S ω) (T : ℝ) : ∀ᶠ t in 𝓝[≥] T, S ω t = S ω T := by
  have hfin := hG.1 (T + 1)
  set A := hfin.toFinset with hA
  have e1 : ∀ᶠ t in 𝓝 T, t < T + 1 := gt_mem_nhds (lt_add_one T)
  have e2 : ∀ᶠ t in 𝓝 T, ∀ j ∈ A, T < arrival ω j → t < arrival ω j := by
    rw [Filter.eventually_all_finset]
    intro j _
    by_cases h : T < arrival ω j
    · filter_upwards [gt_mem_nhds h] with t ht _ using ht
    · exact Filter.Eventually.of_forall fun t h' => absurd h' h
  have e3 : ∀ᶠ t in 𝓝 T, ∀ j ∈ A, present S j ω T → served S j ω t < serviceReq ω j := by
    rw [Filter.eventually_all_finset]
    intro j _
    by_cases h : present S j ω T
    · filter_upwards [(served_continuous S j ω).continuousAt.eventually (gt_mem_nhds h.2)]
        with t ht _ using ht
    · exact Filter.Eventually.of_forall fun t h' => absurd h' h
  have e := e1.and (e2.and e3)
  filter_upwards [nhdsWithin_le_nhds e, self_mem_nhdsWithin] with t ht hTt
  obtain ⟨h1, h2, h3⟩ := ht
  have hTt' : T ≤ t := hTt
  apply sched_eq_of_present_iff σ S ω hG hP
  intro j
  constructor
  · rintro ⟨ha, hs⟩
    have haT : arrival ω j ≤ T := by
      by_contra hc
      rw [not_le] at hc
      have hjA : j ∈ A := by
        rw [hA, Set.Finite.mem_toFinset]; show arrival ω j ≤ T + 1; linarith
      linarith [h2 j hjA hc]
    exact ⟨haT, lt_of_le_of_lt (served_mono S j ω hTt') hs⟩
  · intro hj
    have hjA : j ∈ A := by
      rw [hA, Set.Finite.mem_toFinset]; show arrival ω j ≤ T + 1; linarith [hj.1]
    exact ⟨hj.1.trans hTt', h3 j hjA hj⟩

/-- Locally to the right of `x`, the total service of a finite job set grows at rate `1`
(if the job served at `x` is in `F`) or `0`. -/
theorem sum_served_local {M : ℕ} (σ : Equiv.Perm (Fin M)) (S : Schedule M) (ω : Omega M)
    (hG : GoodAt S ω) (hP : PrioAt σ S ω) (F : Finset (Job M)) {x : ℝ} (hx : 0 ≤ x) :
    ∃ c : ℝ, 0 ≤ c ∧ c ≤ 1 ∧ ((∃ j ∈ F, S ω x = some j) → c = 1) ∧
      ∀ᶠ t in 𝓝[≥] x, ∑ j ∈ F, served S j ω t = ∑ j ∈ F, served S j ω x + c * (t - x) := by
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 (right_const σ S ω hG hP x)
  by_cases hb : ∃ j ∈ F, S ω x = some j
  · obtain ⟨j0, hj0F, hj0⟩ := hb
    refine ⟨1, zero_le_one, le_rfl, fun _ => rfl, ?_⟩
    filter_upwards [Ico_mem_nhdsGE hu] with t ht
    have hS : ∀ s ∈ Set.Ico x t, S ω s = some j0 := by
      intro s hs
      have hs' : S ω s = S ω x := hsub ⟨hs.1, hs.2.trans ht.2⟩
      rw [hs', hj0]
    have hid : ∀ j ∈ F.erase j0, served S j ω t = served S j ω x := by
      intro j hj
      refine served_idle S j ω ht.1 fun s hs h => ?_
      rw [hS s hs] at h
      rw [Finset.mem_erase] at hj
      exact hj.1 (Option.some_injective _ h).symm
    rw [← Finset.add_sum_erase F (fun j => served S j ω t) hj0F,
      ← Finset.add_sum_erase F (fun j => served S j ω x) hj0F,
      served_serving S j0 ω hx ht.1 hS, Finset.sum_congr rfl hid]
    ring
  · simp only [not_exists, not_and] at hb
    refine ⟨0, le_rfl, zero_le_one, fun ⟨j, hj, h⟩ => absurd h (hb j hj), ?_⟩
    filter_upwards [Ico_mem_nhdsGE hu] with t ht
    have hid : ∀ j ∈ F, served S j ω t = served S j ω x := by
      intro j hj
      refine served_idle S j ω ht.1 fun s hs h => ?_
      have hs' : S ω s = S ω x := hsub ⟨hs.1, hs.2.trans ht.2⟩
      rw [hs'] at h
      exact hb j hj h
    rw [Finset.sum_congr rfl hid]
    ring

/-- Busy accounting: if the server works on `F` throughout `[a, b)`, `F` receives `b - a`. -/
theorem busy_sum {M : ℕ} (σ : Equiv.Perm (Fin M)) (S : Schedule M) (ω : Omega M)
    (hG : GoodAt S ω) (hP : PrioAt σ S ω) (F : Finset (Job M)) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hbusy : ∀ t ∈ Set.Ico a b, ∃ j ∈ F, S ω t = some j) :
    ∑ j ∈ F, served S j ω b = ∑ j ∈ F, served S j ω a + (b - a) := by
  have hcont : Continuous fun t => ∑ j ∈ F, served S j ω t - t :=
    (continuous_finset_sum _ fun j _ => served_continuous S j ω).sub continuous_id
  have hder : ∀ x ∈ Set.Ico a b,
      HasDerivWithinAt (fun t => ∑ j ∈ F, served S j ω t - t) 0 (Set.Ici x) x := by
    intro x hx
    obtain ⟨c, -, -, hc1, hev⟩ := sum_served_local σ S ω hG hP F (ha.trans hx.1)
    have hc : c = 1 := hc1 (hbusy x hx)
    have hconst : HasDerivWithinAt (fun _ : ℝ => ∑ j ∈ F, served S j ω x - x) 0 (Set.Ici x) x :=
      hasDerivWithinAt_const _ _ _
    refine hconst.congr_of_eventuallyEq ?_ rfl
    filter_upwards [hev] with t ht
    show ∑ j ∈ F, served S j ω t - t = ∑ j ∈ F, served S j ω x - x
    rw [ht, hc]; ring
  have key := constant_of_has_deriv_right_zero hcont.continuousOn hder b ⟨hab, le_rfl⟩
  have key' : ∑ j ∈ F, served S j ω b - b = ∑ j ∈ F, served S j ω a - a := key
  linarith

/-- Busy accounting, upper bound: `F` never receives more than elapsed time. -/
theorem busy_le {M : ℕ} (σ : Equiv.Perm (Fin M)) (S : Schedule M) (ω : Omega M)
    (hG : GoodAt S ω) (hP : PrioAt σ S ω) (F : Finset (Job M)) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) :
    ∑ j ∈ F, served S j ω b ≤ ∑ j ∈ F, served S j ω a + (b - a) := by
  have hcont : Continuous fun t => ∑ j ∈ F, served S j ω t - t :=
    (continuous_finset_sum _ fun j _ => served_continuous S j ω).sub continuous_id
  have key := image_le_of_liminf_slope_right_le_deriv_boundary
    (f := fun t => ∑ j ∈ F, served S j ω t - t) (a := a) (b := b)
    (B := fun _ => ∑ j ∈ F, served S j ω a - a) (B' := fun _ => 0)
    hcont.continuousOn le_rfl continuousOn_const (fun x _ => hasDerivWithinAt_const _ _ _) ?_
    ⟨hab, le_rfl⟩
  · have k2 : ∑ j ∈ F, served S j ω b - b ≤ ∑ j ∈ F, served S j ω a - a := key
    linarith
  · intro x hx r hr
    obtain ⟨c, -, hc1, -, hev⟩ := sum_served_local σ S ω hG hP F (ha.trans hx.1)
    refine Filter.Eventually.frequently ?_
    have hev' : ∀ᶠ t in 𝓝[>] x,
        ∑ j ∈ F, served S j ω t = ∑ j ∈ F, served S j ω x + c * (t - x) :=
      nhdsWithin_mono _ Set.Ioi_subset_Ici_self hev
    filter_upwards [hev', self_mem_nhdsWithin] with t ht htx
    have htx' : 0 < t - x := sub_pos.2 htx
    rw [slope_def_field, ht, div_lt_iff₀ htx']
    nlinarith [mul_pos hr htx', mul_nonneg (sub_nonneg.2 hc1) htx'.le]

/-! ### C1a: finitely many arrivals in bounded time, almost surely -/

theorem tendsto_partial_sum_of_frequently {x : ℕ → ℝ} (hpos : ∀ m, 0 ≤ x m)
    (hfr : ∃ᶠ m in atTop, 1 ≤ x m) :
    Tendsto (fun n => ∑ m ∈ Finset.range (n + 1), x m) atTop atTop := by
  apply tendsto_atTop_atTop_of_monotone'
  · intro a b hab
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      (fun m _ _ => hpos m)
  · rintro ⟨B, hB⟩
    have hinf : Set.Infinite {m | 1 ≤ x m} := Nat.frequently_atTop_iff_infinite.1 hfr
    obtain ⟨t, hts, htc⟩ := hinf.exists_subset_card_eq (⌈B⌉₊ + 1)
    have hsub : t ⊆ Finset.range (t.sup id + 1) := fun m hm =>
      Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := id) hm))
    have h1 : ∑ m ∈ t, x m ≤ ∑ m ∈ Finset.range (t.sup id + 1), x m :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => hpos m)
    have h2 := Finset.card_nsmul_le_sum t x 1 (fun m hm => hts hm)
    rw [nsmul_one, htc] at h2
    have h3 := hB ⟨t.sup id, rfl⟩
    push_cast at h2
    linarith [Nat.le_ceil B]

theorem finite_le_of_tendsto {f : ℕ → ℝ} (hf : Tendsto f atTop atTop) (T : ℝ) :
    Set.Finite {n | f n ≤ T} := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hf.eventually_gt_atTop T)
  refine (Set.finite_lt_nat N).subset fun n hn => ?_
  by_contra h
  simp only [Set.mem_setOf_eq, not_lt] at h hn
  linarith [hN n h]

theorem jobs_finite_of_tendsto {M : ℕ} (ω : Omega M)
    (h : ∀ i : Fin M, Tendsto (fun n => arrival ω (i, n)) atTop atTop) (T : ℝ) :
    Set.Finite {j : Job M | arrival ω j ≤ T} := by
  have hsub : {j : Job M | arrival ω j ≤ T} ⊆
      ⋃ i : Fin M, (fun n => (i, n)) '' {n | arrival ω (i, n) ≤ T} := by
    rintro ⟨i, n⟩ hj
    exact Set.mem_iUnion.2 ⟨i, n, hj, rfl⟩
  exact (Set.finite_iUnion fun i => (finite_le_of_tendsto (h i) T).image _).subset hsub

theorem expMeasure_Ici_one_ne_zero {r : ℝ} (hr : 0 < r) : expMeasure r (Set.Ici 1) ≠ 0 := by
  haveI := isProbabilityMeasure_expMeasure hr
  intro h0
  have hle : expMeasure r (Set.Ioi 1) = 0 := measure_mono_null Set.Ioi_subset_Ici_self h0
  rw [← Set.compl_Iic, prob_compl_eq_zero_iff measurableSet_Iic, ← ofReal_cdf,
    cdf_expMeasure_eq hr] at hle
  simp only [zero_le_one, if_true, mul_one] at hle
  have hexp := Real.exp_pos (-r)
  have := (ENNReal.ofReal_eq_one).1 hle
  linarith

/-- Second Borel-Cantelli: a.s. infinitely many interarrival times of class `i` are `≥ 1`. -/
theorem ae_frequently_ge_one (D : Data) (i : Fin D.M) :
    ∀ᵐ ω ∂D.P, ∃ᶠ m in atTop, 1 ≤ ω.1 (i, m) := by
  haveI : ∀ j : Job D.M, IsProbabilityMeasure (expMeasure (D.lam j.1)) :=
    fun j => isProbabilityMeasure_expMeasure (D.lam_pos j.1)
  haveI : ∀ j : Job D.M, IsProbabilityMeasure (expMeasure (D.mu j.1)) :=
    fun j => isProbabilityMeasure_expMeasure (D.mu_pos j.1)
  set μ0 : Measure (Job D.M → ℝ) := Measure.infinitePi fun j : Job D.M => expMeasure (D.lam j.1)
    with hμ0
  have hmap : D.P.map Prod.fst = μ0 := by
    unfold Data.P
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  set s : ℕ → Set (Job D.M → ℝ) := fun m => (fun x => x (i, m)) ⁻¹' Set.Ici 1 with hs
  have hsm : ∀ m, MeasurableSet (s m) := fun m => measurable_pi_apply _ measurableSet_Ici
  have hF : iIndepFun (fun m (x : Job D.M → ℝ) => x (i, m)) μ0 := by
    have h0 := iIndepFun_infinitePi (P := fun j : Job D.M => expMeasure (D.lam j.1))
      (X := fun _ (y : ℝ) => y) (fun _ => measurable_id)
    exact h0.precomp (g := fun m : ℕ => (i, m)) (fun a b h => (Prod.ext_iff.1 h).2)
  have hind : iIndepSet s μ0 := by
    rw [iIndepSet_iff_meas_biInter hsm]
    intro S
    exact (iIndepFun_iff_measure_inter_preimage_eq_mul.1 hF) S
      (sets := fun _ => Set.Ici 1) (fun _ _ => measurableSet_Ici)
  have hval : ∀ m, μ0 (s m) = expMeasure (D.lam i) (Set.Ici 1) := by
    intro m
    rw [hs, ← Measure.map_apply (measurable_pi_apply _) measurableSet_Ici, hμ0,
      Measure.infinitePi_map_eval]
  have hsum : (∑' m, μ0 (s m)) = ⊤ := by
    simp_rw [hval]
    exact ENNReal.tsum_const_eq_top_of_ne_zero (expMeasure_Ici_one_ne_zero (D.lam_pos i))
  have hls := measure_limsup_eq_one hsm hind hsum
  have hLm : MeasurableSet (limsup s atTop) := by
    rw [Filter.limsup_eq_iInf_iSup_of_nat]
    exact MeasurableSet.iInter fun n => MeasurableSet.iUnion fun k =>
      MeasurableSet.iUnion fun _ => hsm k
  have hae : ∀ᵐ x ∂μ0, ∃ᶠ m in atTop, 1 ≤ x (i, m) := by
    rw [ae_iff]
    have : {a : Job D.M → ℝ | ¬ ∃ᶠ m in atTop, 1 ≤ a (i, m)} = (limsup s atTop)ᶜ := by
      ext a
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, mem_limsup_iff_frequently_mem, hs,
        Set.mem_preimage, Set.mem_Ici]
    rw [this, prob_compl_eq_zero_iff hLm]
    exact hls
  rw [← hmap] at hae
  exact ae_of_ae_map measurable_fst.aemeasurable hae

theorem ae_arrival_tendsto (D : Data) :
    ∀ᵐ ω ∂D.P, ∀ i : Fin D.M, Tendsto (fun n => arrival ω (i, n)) atTop atTop := by
  rw [ae_all_iff]
  intro i
  filter_upwards [ae_frequently_ge_one D i, ae_interarrival_pos D] with ω h1 h2
  exact tendsto_partial_sum_of_frequently (fun m => (h2 (i, m)).le) h1

theorem ae_arrival_finite (D : Data) :
    ∀ᵐ ω ∂D.P, ∀ T : ℝ, Set.Finite {j : Job D.M | arrival ω j ≤ T} := by
  filter_upwards [ae_arrival_tendsto D] with ω h T using jobs_finite_of_tendsto ω h T

/-! ### C1d: work accounting for a class set `g` -/

theorem served_eq_zero_of_le_arrival {M : ℕ} (S : Schedule M) (ω : Omega M)
    (hpres : ∀ (t : ℝ) (j : Job M), S ω t = some j → present S j ω t) (j : Job M) {t : ℝ}
    (ht : t ≤ arrival ω j) : served S j ω t = 0 := by
  classical
  unfold served
  have hemp : {s : ℝ | S ω s = some j} ∩ Set.Ico 0 t = ∅ := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Ico, Set.mem_empty_iff_false,
      iff_false, not_and]
    intro hs _ hst
    have := (hpres s j hs).1
    linarith
  rw [hemp, measure_empty, ENNReal.toReal_zero]

theorem served_le_req {M : ℕ} (S : Schedule M) (ω : Omega M)
    (hpres : ∀ (t : ℝ) (j : Job M), S ω t = some j → present S j ω t) (j : Job M)
    (hreq : 0 ≤ serviceReq ω j) (t : ℝ) : served S j ω t ≤ serviceReq ω j := by
  classical
  by_contra hlt
  push_neg at hlt
  have ht0 : 0 ≤ t := by
    by_contra h
    push_neg at h
    rw [served_of_nonpos S j ω h.le] at hlt
    linarith
  obtain ⟨c, hc, hcv⟩ := intermediate_value_Icc ht0 (served_continuous S j ω).continuousOn
    ⟨by rw [served_of_nonpos S j ω le_rfl]; exact hreq, hlt.le⟩
  have hidle := served_idle S j ω hc.2 fun s hs h => by
    have hp := (hpres s j h).2
    have := served_mono S j ω hs.1
    linarith
  linarith

/-- A job predicate closed upward under the priority order of `σ` (FCFS within a class). -/
def UpClosed {M : ℕ} (σ : Equiv.Perm (Fin M)) (A : Job M → Prop) : Prop :=
  ∀ j j' : Job M, A j' → (σ.symm j.1 < σ.symm j'.1 ∨ (j.1 = j'.1 ∧ j.2 ≤ j'.2)) → A j

theorem serves_upclosed {M : ℕ} (σ : Equiv.Perm (Fin M)) (S : Schedule M) (ω : Omega M)
    (hG : GoodAt S ω) (hP : PrioAt σ S ω) {A : Job M → Prop} (hA : UpClosed σ A) {t : ℝ}
    {j' : Job M} (hj' : A j') (hpr : present S j' ω t) : ∃ j, A j ∧ S ω t = some j := by
  classical
  cases h : S ω t with
  | none => exact absurd hpr (((hG.2.2 t).1 h) j')
  | some j => exact ⟨j, hA j j' hj' (hP t j j' h hpr), rfl⟩

/-- Work of jobs in `A` arriving in `[s, t)`. -/
noncomputable def workP {M : ℕ} (ω : Omega M) (A : Job M → Prop) (s t : ℝ) : ℝ :=
  ∑' j : Job M, Set.indicator {j : Job M | A j ∧ s ≤ arrival ω j ∧ arrival ω j < t}
    (serviceReq ω) j

/-- Service given to jobs in `A` during `[0, t)`. -/
noncomputable def servP {M : ℕ} (S : Schedule M) (ω : Omega M) (A : Job M → Prop) (t : ℝ) : ℝ :=
  ∑' j : Job M, Set.indicator {j : Job M | A j} (fun j => served S j ω t) j

/-- Remaining `A`-work just before `t` (system empty at time 0). -/
noncomputable def remP {M : ℕ} (S : Schedule M) (ω : Omega M) (A : Job M → Prop) (t : ℝ) : ℝ :=
  workP ω A 0 t - servP S ω A t

theorem workP_eq_sum {M : ℕ} (ω : Omega M) (A : Job M → Prop) {s t : ℝ} (F : Finset (Job M))
    (hF : ∀ j : Job M, arrival ω j < t → j ∈ F) :
    workP ω A s t = ∑ j ∈ F,
      Set.indicator {j : Job M | A j ∧ s ≤ arrival ω j ∧ arrival ω j < t} (serviceReq ω) j := by
  classical
  unfold workP
  apply tsum_eq_sum
  intro j hj
  apply Set.indicator_of_notMem
  rintro ⟨-, -, h⟩
  exact hj (hF j h)

open Classical in
theorem servP_eq_sum {M : ℕ} (S : Schedule M) (ω : Omega M)
    (hpres : ∀ (t : ℝ) (j : Job M), S ω t = some j → present S j ω t) (A : Job M → Prop)
    {t : ℝ} (F : Finset (Job M)) (hF : ∀ j : Job M, arrival ω j < t → j ∈ F) :
    servP S ω A t = ∑ j ∈ F.filter (fun j => A j), served S j ω t := by
  classical
  rw [Finset.sum_filter]
  unfold servP
  rw [tsum_eq_sum (s := F)]
  · refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : A j <;> simp [Set.indicator_apply, h]
  · intro j hj
    have hnot : ¬ arrival ω j < t := fun h => hj (hF j h)
    by_cases h : A j
    · rw [Set.indicator_of_mem (show j ∈ {j : Job M | A j} from h)]
      exact served_eq_zero_of_le_arrival S ω hpres j (not_lt.1 hnot)
    · exact Set.indicator_of_notMem (show j ∉ {j : Job M | A j} from h) _

theorem workP_add {M : ℕ} (ω : Omega M) (hfin : ∀ T : ℝ, Set.Finite {j : Job M | arrival ω j ≤ T})
    (A : Job M → Prop) {r s t : ℝ} (hrs : r ≤ s) (hst : s ≤ t) :
    workP ω A r t = workP ω A r s + workP ω A s t := by
  classical
  set F := (hfin t).toFinset
  have hF : ∀ j : Job M, arrival ω j < t → j ∈ F := fun j h => (hfin t).mem_toFinset.2 h.le
  have hF' : ∀ j : Job M, arrival ω j < s → j ∈ F := fun j h => hF j (lt_of_lt_of_le h hst)
  rw [workP_eq_sum ω A F hF, workP_eq_sum ω A F hF', workP_eq_sum ω A F hF,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Set.indicator_apply, Set.mem_setOf_eq]
  by_cases h1 : A j <;> by_cases h2 : arrival ω j < s <;> by_cases h3 : arrival ω j < t <;>
    by_cases h4 : r ≤ arrival ω j <;> simp [h1, h2, h3, h4] <;> linarith

theorem remP_accounting {M : ℕ} (S : Schedule M) (ω : Omega M)
    (hfin : ∀ T : ℝ, Set.Finite {j : Job M | arrival ω j ≤ T}) (A : Job M → Prop) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) :
    remP S ω A t = remP S ω A s + workP ω A s t - (servP S ω A t - servP S ω A s) := by
  classical
  unfold remP
  rw [workP_add ω hfin A hs hst]
  ring

theorem remP_nonneg {M : ℕ} (S : Schedule M) (ω : Omega M) (hG : GoodAt S ω)
    (harr : ∀ j : Job M, 0 ≤ arrival ω j) (hreq : ∀ j : Job M, 0 ≤ serviceReq ω j)
    (A : Job M → Prop) (t : ℝ) : 0 ≤ remP S ω A t := by
  classical
  set F := (hG.1 t).toFinset
  have hF : ∀ j : Job M, arrival ω j < t → j ∈ F := fun j h => (hG.1 t).mem_toFinset.2 h.le
  unfold remP
  rw [workP_eq_sum ω A F hF, servP_eq_sum S ω hG.2.1 A F hF, Finset.sum_filter,
    sub_nonneg]
  refine Finset.sum_le_sum fun j _ => ?_
  simp only [Set.indicator_apply, Set.mem_setOf_eq]
  by_cases h1 : A j
  · by_cases h3 : arrival ω j < t
    · simp only [h1, h3, harr j, and_self, if_true]
      exact served_le_req S ω hG.2.1 j (hreq j) t
    · simp only [h1, h3, and_false, if_false, if_true]
      exact (served_eq_zero_of_le_arrival S ω hG.2.1 j (not_lt.1 h3)).le
  · simp [h1]

/-- Service to `g` over `[s, t)` is at most `t - s`. -/
theorem servP_le {M : ℕ} (σ : Equiv.Perm (Fin M)) (S : Schedule M) (ω : Omega M)
    (hG : GoodAt S ω) (hP : PrioAt σ S ω) (A : Job M → Prop) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) : servP S ω A t - servP S ω A s ≤ t - s := by
  classical
  set F := (hG.1 t).toFinset
  have hF : ∀ j : Job M, arrival ω j < t → j ∈ F := fun j h => (hG.1 t).mem_toFinset.2 h.le
  have hF' : ∀ j : Job M, arrival ω j < s → j ∈ F := fun j h => hF j (lt_of_lt_of_le h hst)
  rw [servP_eq_sum S ω hG.2.1 A F hF, servP_eq_sum S ω hG.2.1 A F hF']
  linarith [busy_le σ S ω hG hP (F.filter fun j => A j) hs hst]

/-- If the server works on `g` throughout `[s, t)`, then `g` receives exactly `t - s`. -/
theorem servP_busy {M : ℕ} (σ : Equiv.Perm (Fin M)) (S : Schedule M) (ω : Omega M)
    (hG : GoodAt S ω) (hP : PrioAt σ S ω) (A : Job M → Prop) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (hbusy : ∀ u ∈ Set.Ico s t, ∃ j : Job M, A j ∧ S ω u = some j) :
    servP S ω A t - servP S ω A s = t - s := by
  classical
  set F := (hG.1 t).toFinset
  have hF : ∀ j : Job M, arrival ω j < t → j ∈ F := fun j h => (hG.1 t).mem_toFinset.2 h.le
  have hF' : ∀ j : Job M, arrival ω j < s → j ∈ F := fun j h => hF j (lt_of_lt_of_le h hst)
  rw [servP_eq_sum S ω hG.2.1 A F hF, servP_eq_sum S ω hG.2.1 A F hF']
  have hb : ∀ u ∈ Set.Ico s t, ∃ j ∈ F.filter (fun j => A j), S ω u = some j := by
    intro u hu
    obtain ⟨j, hjg, hj⟩ := hbusy u hu
    refine ⟨j, Finset.mem_filter.2 ⟨hF j ?_, hjg⟩, hj⟩
    exact lt_of_le_of_lt (hG.2.1 u j hj).1 hu.2
  linarith [busy_sum σ S ω hG hP (F.filter fun j => A j) hs hst hb]

theorem workP_nonneg {M : ℕ} (ω : Omega M) (hreq : ∀ j : Job M, 0 ≤ serviceReq ω j)
    (A : Job M → Prop) (s t : ℝ) : 0 ≤ workP ω A s t :=
  tsum_nonneg fun j => Set.indicator_nonneg (fun j _ => hreq j) j

theorem workP_self {M : ℕ} (ω : Omega M) (A : Job M → Prop) (s : ℝ) : workP ω A s s = 0 := by
  classical
  unfold workP
  refine (tsum_congr fun j => Set.indicator_of_notMem ?_ _).trans tsum_zero
  rintro ⟨-, h1, h2⟩
  linarith

theorem servP_mono {M : ℕ} (S : Schedule M) (ω : Omega M) (hG : GoodAt S ω)
    (A : Job M → Prop) {s t : ℝ} (hst : s ≤ t) : servP S ω A s ≤ servP S ω A t := by
  classical
  set F := (hG.1 t).toFinset
  have hF : ∀ j : Job M, arrival ω j < t → j ∈ F := fun j h => (hG.1 t).mem_toFinset.2 h.le
  have hF' : ∀ j : Job M, arrival ω j < s → j ∈ F := fun j h => hF j (lt_of_lt_of_le h hst)
  rw [servP_eq_sum S ω hG.2.1 A F hF, servP_eq_sum S ω hG.2.1 A F hF']
  exact Finset.sum_le_sum fun j _ => served_mono S j ω hst

theorem remP_zero {M : ℕ} (S : Schedule M) (ω : Omega M) (A : Job M → Prop) :
    remP S ω A 0 = 0 := by
  classical
  have h0 : ∀ j : Job M, served S j ω 0 = 0 := fun j => served_of_nonpos S j ω le_rfl
  unfold remP servP
  rw [workP_self]
  simp [h0]

theorem exists_present_of_remP_pos {M : ℕ} (S : Schedule M) (ω : Omega M) (hG : GoodAt S ω)
    (harr : ∀ j : Job M, 0 ≤ arrival ω j) (A : Job M → Prop) {v : ℝ}
    (hv : 0 < remP S ω A v) : ∃ j : Job M, A j ∧ present S j ω v := by
  classical
  set F := (hG.1 v).toFinset
  have hF : ∀ j : Job M, arrival ω j < v → j ∈ F := fun j h => (hG.1 v).mem_toFinset.2 h.le
  unfold remP at hv
  rw [workP_eq_sum ω A F hF, servP_eq_sum S ω hG.2.1 A F hF, Finset.sum_filter, sub_pos] at hv
  obtain ⟨j, -, hj⟩ := Finset.exists_lt_of_sum_lt hv
  simp only [Set.indicator_apply, Set.mem_setOf_eq] at hj
  by_cases h1 : A j
  · by_cases h3 : arrival ω j < v
    · simp only [h1, h3, harr j, and_self, if_true] at hj
      exact ⟨j, h1, h3.le, hj⟩
    · simp only [h1, h3, and_false, if_false, if_true] at hj
      linarith [served_nonneg S j ω v]
  · simp [h1] at hj

theorem upClosed_class {M : ℕ} (σ : Equiv.Perm (Fin M)) (g : Finset (Fin M))
    (hg : ∀ i i' : Fin M, i' ∈ g → σ.symm i < σ.symm i' → i ∈ g) :
    UpClosed σ (fun j : Job M => j.1 ∈ g) := by
  intro j j' hj' h
  rcases h with h | ⟨h, -⟩
  · exact hg _ _ hj' h
  · show j.1 ∈ g
    rw [h]
    exact hj'

/-- Reflected (Lindley / Reich) `g`-backlog just before `t`, system empty at time 0. -/
noncomputable def backlogP {M : ℕ} (ω : Omega M) (A : Job M → Prop) (t : ℝ) : ℝ :=
  max 0 (sSup ((fun s => workP ω A s t - (t - s)) '' Set.Icc 0 t))

/-- **C1d (Reich).** For a priority-upward-closed job set `A`, the remaining `g`-work just
before `t` is the reflected backlog. -/
theorem backlogP_eq_remP {M : ℕ} (σ : Equiv.Perm (Fin M)) (S : Schedule M) (ω : Omega M)
    (hG : GoodAt S ω) (hP : PrioAt σ S ω) (harr : ∀ j : Job M, 0 ≤ arrival ω j)
    (hreq : ∀ j : Job M, 0 ≤ serviceReq ω j) (A : Job M → Prop)
    (hA : UpClosed σ A) {t : ℝ} (ht : 0 ≤ t) :
    backlogP ω A t = remP S ω A t := by
  have hfin := hG.1
  unfold backlogP
  have hne : ((fun s => workP ω A s t - (t - s)) '' Set.Icc 0 t).Nonempty :=
    ⟨_, Set.mem_image_of_mem _ ⟨le_rfl, ht⟩⟩
  have hbdd : BddAbove ((fun s => workP ω A s t - (t - s)) '' Set.Icc 0 t) := by
    refine ⟨workP ω A 0 t, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    have h1 := workP_add ω hfin A hs.1 hs.2
    have h2 := workP_nonneg ω hreq A 0 s
    show workP ω A s t - (t - s) ≤ workP ω A 0 t
    linarith [hs.2]
  have hlow : ∀ s ∈ Set.Icc 0 t, workP ω A s t - (t - s) ≤ remP S ω A t := by
    intro s hs
    have h1 := remP_accounting S ω hfin A hs.1 hs.2
    have h2 := remP_nonneg S ω hG harr hreq A s
    have h3 := servP_le σ S ω hG hP A hs.1 hs.2
    linarith
  apply le_antisymm
  · exact max_le (remP_nonneg S ω hG harr hreq A t)
      (csSup_le hne (by rintro _ ⟨s, hs, rfl⟩; exact hlow s hs))
  · by_cases hpos : remP S ω A t ≤ 0
    · exact hpos.trans (le_max_left _ _)
    push_neg at hpos
    refine le_trans ?_ (le_max_right _ _)
    set Z := {u : ℝ | u ∈ Set.Icc 0 t ∧ remP S ω A u ≤ 0} with hZ
    have hZ0 : (0 : ℝ) ∈ Z := ⟨⟨le_rfl, ht⟩, (remP_zero S ω A).le⟩
    have hZne : Z.Nonempty := ⟨0, hZ0⟩
    have hZbdd : BddAbove Z := ⟨t, fun u hu => hu.1.2⟩
    set s0 := sSup Z with hs0
    have hs0nn : 0 ≤ s0 := le_csSup hZbdd hZ0
    have hs0t : s0 ≤ t := csSup_le hZne fun u hu => hu.1.2
    have hrem0 : remP S ω A s0 ≤ 0 := by
      set F := (hfin s0).toFinset
      have hev : ∀ᶠ u in 𝓝[<] s0, ∀ j ∈ F, arrival ω j < s0 → arrival ω j < u := by
        rw [Filter.eventually_all_finset]
        intro j _
        by_cases h : arrival ω j < s0
        · filter_upwards [nhdsWithin_le_nhds (lt_mem_nhds h)] with u hu _ using hu
        · exact Filter.Eventually.of_forall fun u h' => absurd h' h
      obtain ⟨b, hb, hbsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hev
      obtain ⟨u, huZ, hbu⟩ := exists_lt_of_lt_csSup hZne hb
      have hus0 : u ≤ s0 := le_csSup hZbdd huZ
      have hw : workP ω A u s0 = 0 := by
        rcases eq_or_lt_of_le hus0 with h | h
        · rw [h]; exact workP_self ω A s0
        · unfold workP
          refine (tsum_congr fun j => Set.indicator_of_notMem ?_ _).trans tsum_zero
          rintro ⟨-, h1, h2⟩
          have hjF : j ∈ F := (hfin s0).mem_toFinset.2 h2.le
          have hu : ∀ j ∈ F, arrival ω j < s0 → arrival ω j < u := hbsub ⟨hbu, h⟩
          linarith [hu j hjF h2]
      have hacc := remP_accounting S ω hfin A huZ.1.1 hus0
      have hmono := servP_mono S ω hG A hus0
      linarith [huZ.2]
    have hs0lt : s0 < t := by
      rcases eq_or_lt_of_le hs0t with h | h
      · rw [h] at hrem0; linarith
      · exact h
    have hbusy : ∀ v ∈ Set.Ioo s0 t, ∃ j : Job M, A j ∧ S ω v = some j := by
      intro v hv
      have hvpos : 0 < remP S ω A v := by
        by_contra hc
        push_neg at hc
        have : v ≤ s0 := le_csSup hZbdd ⟨⟨hs0nn.trans hv.1.le, hv.2.le⟩, hc⟩
        linarith [hv.1]
      obtain ⟨j', hj'g, hj'p⟩ := exists_present_of_remP_pos S ω hG harr A hvpos
      exact serves_upclosed σ S ω hG hP hA hj'g hj'p
    have hserv : t - s0 ≤ servP S ω A t - servP S ω A s0 := by
      refine le_of_forall_pos_lt_add fun ε hε => ?_
      have he : 0 < min (ε / 2) ((t - s0) / 2) := lt_min (half_pos hε) (by linarith)
      have he2 : min (ε / 2) ((t - s0) / 2) ≤ (t - s0) / 2 := min_le_right _ _
      have he1 : min (ε / 2) ((t - s0) / 2) ≤ ε / 2 := min_le_left _ _
      have hb := servP_busy σ S ω hG hP A (s := s0 + min (ε / 2) ((t - s0) / 2)) (t := t)
        (by linarith) (by linarith) (fun u hu => hbusy u ⟨by linarith [hu.1], hu.2⟩)
      have hm := servP_mono S ω hG A (s := s0) (t := s0 + min (ε / 2) ((t - s0) / 2))
        (by linarith)
      linarith
    have hacc := remP_accounting S ω hfin A hs0nn hs0t
    have hle : workP ω A s0 t - (t - s0) ≤
        sSup ((fun s => workP ω A s t - (t - s)) '' Set.Icc 0 t) :=
      le_csSup hbdd ⟨s0, ⟨hs0nn, hs0t⟩, rfl⟩
    linarith

/-- Work of classes in `g` arriving in `[s, t)`. -/
noncomputable def workG {M : ℕ} (ω : Omega M) (g : Finset (Fin M)) (s t : ℝ) : ℝ :=
  workP ω (fun j => j.1 ∈ g) s t

/-- Reflected (Lindley / Reich) `g`-backlog just before `t`, system empty at time 0. -/
noncomputable def backlog {M : ℕ} (ω : Omega M) (g : Finset (Fin M)) (t : ℝ) : ℝ :=
  max 0 (sSup ((fun s => workG ω g s t - (t - s)) '' Set.Icc 0 t))

theorem backlog_eq_remP {M : ℕ} (σ : Equiv.Perm (Fin M)) (S : Schedule M) (ω : Omega M)
    (hG : GoodAt S ω) (hP : PrioAt σ S ω) (harr : ∀ j : Job M, 0 ≤ arrival ω j)
    (hreq : ∀ j : Job M, 0 ≤ serviceReq ω j) (g : Finset (Fin M))
    (hg : ∀ i i' : Fin M, i' ∈ g → σ.symm i < σ.symm i' → i ∈ g) {t : ℝ} (ht : 0 ≤ t) :
    backlog ω g t = remP S ω (fun j => j.1 ∈ g) t :=
  backlogP_eq_remP σ S ω hG hP harr hreq _ (upClosed_class σ g hg) ht


/-! ### C1e: the response time of a class-`c` job is a delay busy period -/

/-- Delay busy period of the classes `h` started at time `t` by initial work `x`. -/
noncomputable def delayBP {M : ℕ} (ω : Omega M) (h : Finset (Fin M)) (t x : ℝ) : ℝ :=
  sInf {u : ℝ | 0 ≤ u ∧ x + workG ω h t (t + u) ≤ u}

theorem arrival_lt_of_lt {M : ℕ} (ω : Omega M) (hpos : ∀ j : Job M, 0 < ω.1 j) (i : Fin M)
    {m m' : ℕ} (h : m < m') : arrival ω (i, m) < arrival ω (i, m') := by
  unfold arrival
  exact Finset.sum_lt_sum_of_subset (i := m') (Finset.range_mono (show m + 1 ≤ m' + 1 by omega))
    (Finset.mem_range.2 (by omega)) (fun hm => by rw [Finset.mem_range] at hm; omega)
    (hpos _) (fun j _ _ => (hpos _).le)

/-- Jobs of priority at least that of `(c, n)`: higher classes `h`, plus class `c` up to `n`. -/
def AH {M : ℕ} (h : Finset (Fin M)) (c : Fin M) (n : ℕ) (j : Job M) : Prop :=
  j.1 ∈ h ∨ (j.1 = c ∧ j.2 ≤ n)

theorem upClosed_AH {M : ℕ} (σ : Equiv.Perm (Fin M)) (h : Finset (Fin M)) (c : Fin M) (n : ℕ)
    (hh : ∀ i, i ∈ h ↔ σ.symm i < σ.symm c) : UpClosed σ (AH h c n) := by
  intro j j' hj' hpr
  rcases hj' with hj' | ⟨hj'c, hj'n⟩
  · left
    rw [hh] at hj' ⊢
    rcases hpr with hpr | ⟨hpr, -⟩
    · exact hpr.trans hj'
    · rw [hpr]; exact hj'
  · rcases hpr with hpr | ⟨hpr1, hpr2⟩
    · left; rw [hh, ← hj'c]; exact hpr
    · right; exact ⟨hpr1.trans hj'c, hpr2.trans hj'n⟩

theorem only_J {M : ℕ} (σ : Equiv.Perm (Fin M)) (S : Schedule M) (ω : Omega M)
    (hP : PrioAt σ S ω) (h : Finset (Fin M)) (c : Fin M) (n : ℕ)
    (hh : ∀ i, i ∈ h ↔ σ.symm i < σ.symm c) {s : ℝ} (hs : S ω s = some (c, n))
    {j : Job M} (hj : AH h c n j) (hpr : present S j ω s) : j = (c, n) := by
  have h2 : σ.symm j.1 < σ.symm (c, n).1 ∨ (j.1 = (c, n).1 ∧ j.2 ≤ (c, n).2) := by
    rcases hj with hj | hj
    · left; exact (hh _).1 hj
    · right; exact hj
  exact (prio_antisymm σ (c, n) j (hP s (c, n) j hs hpr) h2).symm

open Classical in
theorem remP_eq_sum {M : ℕ} (S : Schedule M) (ω : Omega M) (hG : GoodAt S ω)
    (harr : ∀ j : Job M, 0 ≤ arrival ω j) (A : Job M → Prop) {t : ℝ} (F : Finset (Job M))
    (hF : ∀ j : Job M, arrival ω j < t → j ∈ F) :
    remP S ω A t = ∑ j ∈ F,
      (if A j ∧ arrival ω j < t then serviceReq ω j - served S j ω t else 0) := by
  classical
  unfold remP
  rw [workP_eq_sum ω A F hF, servP_eq_sum S ω hG.2.1 A F hF, Finset.sum_filter,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Set.indicator_apply, Set.mem_setOf_eq]
  by_cases h1 : A j
  · by_cases h3 : arrival ω j < t
    · simp [h1, h3, harr j]
    · simp [h1, h3, served_eq_zero_of_le_arrival S ω hG.2.1 j (not_lt.1 h3)]
  · simp [h1]

open Classical in
theorem remP_ge_term {M : ℕ} (S : Schedule M) (ω : Omega M) (hG : GoodAt S ω)
    (harr : ∀ j : Job M, 0 ≤ arrival ω j) (hreq : ∀ j : Job M, 0 ≤ serviceReq ω j)
    (A : Job M → Prop) {t : ℝ} {j : Job M} (hj : A j) (hjt : arrival ω j < t) :
    serviceReq ω j - served S j ω t ≤ remP S ω A t := by
  classical
  set F := (hG.1 t).toFinset
  have hF : ∀ j : Job M, arrival ω j < t → j ∈ F := fun j h => (hG.1 t).mem_toFinset.2 h.le
  rw [remP_eq_sum S ω hG harr A F hF]
  have hnn : ∀ i ∈ F, 0 ≤
      (if A i ∧ arrival ω i < t then serviceReq ω i - served S i ω t else 0) := by
    intro i _
    split_ifs
    · exact sub_nonneg.2 (served_le_req S ω hG.2.1 i (hreq i) t)
    · exact le_rfl
  have key := Finset.single_le_sum hnn (hF j hjt)
  rwa [if_pos ⟨hj, hjt⟩] at key

theorem remP_AH_T {M : ℕ} (σ : Equiv.Perm (Fin M)) (S : Schedule M) (ω : Omega M)
    (hG : GoodAt S ω) (harr : ∀ j : Job M, 0 ≤ arrival ω j)
    (hinc : ∀ (i : Fin M) (m m' : ℕ), m < m' → arrival ω (i, m) < arrival ω (i, m'))
    (g h : Finset (Fin M)) (c : Fin M) (n : ℕ)
    (hg : ∀ i, i ∈ g ↔ σ.symm i ≤ σ.symm c) (hh : ∀ i, i ∈ h ↔ σ.symm i < σ.symm c) :
    remP S ω (AH h c n) (arrival ω (c, n)) =
      remP S ω (fun j => j.1 ∈ g) (arrival ω (c, n)) := by
  classical
  have hAg : ∀ j : Job M, arrival ω j < arrival ω (c, n) → (AH h c n j ↔ j.1 ∈ g) := by
    intro j hjT
    constructor
    · rintro (hj | ⟨hjc, -⟩)
      · rw [hg]; exact ((hh _).1 hj).le
      · rw [hg, hjc]
    · intro hj
      rw [hg] at hj
      rcases hj.lt_or_eq with hlt | heq
      · left; exact (hh _).2 hlt
      · right
        have hjc : j.1 = c := σ.symm.injective heq
        refine ⟨hjc, ?_⟩
        by_contra hn
        push_neg at hn
        have h1 := hinc c n j.2 hn
        have hj' : ((c, j.2) : Job M) = j := by rw [← hjc]
        rw [hj'] at h1
        linarith
  set F := (hG.1 (arrival ω (c, n))).toFinset
  have hF : ∀ j : Job M, arrival ω j < arrival ω (c, n) → j ∈ F :=
    fun j hj => (hG.1 _).mem_toFinset.2 hj.le
  rw [remP_eq_sum S ω hG harr _ F hF, remP_eq_sum S ω hG harr _ F hF]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h3 : arrival ω j < arrival ω (c, n)
  · have e := hAg j h3
    by_cases h1 : AH h c n j
    · have h2 : j.1 ∈ g := e.1 h1
      rw [if_pos ⟨h1, h3⟩, if_pos ⟨h2, h3⟩]
    · have h2 : j.1 ∉ g := fun h2 => h1 (e.2 h2)
      rw [if_neg (fun hc => h1 hc.1), if_neg (fun hc => h2 hc.1)]
  · rw [if_neg (fun hc => h3 hc.2), if_neg (fun hc => h3 hc.2)]

theorem workP_AH {M : ℕ} (σ : Equiv.Perm (Fin M)) (ω : Omega M)
    (hfin : ∀ T : ℝ, Set.Finite {j : Job M | arrival ω j ≤ T})
    (hinc : ∀ (i : Fin M) (m m' : ℕ), m < m' → arrival ω (i, m) < arrival ω (i, m'))
    (h : Finset (Fin M)) (c : Fin M) (n : ℕ) (hh : ∀ i, i ∈ h ↔ σ.symm i < σ.symm c)
    {t : ℝ} (hTt : arrival ω (c, n) < t) :
    workP ω (AH h c n) (arrival ω (c, n)) t =
      serviceReq ω (c, n) + workG ω h (arrival ω (c, n)) t := by
  classical
  have hc_notin : c ∉ h := fun hc => lt_irrefl _ ((hh c).1 hc)
  set F := (hfin t).toFinset
  have hF : ∀ j : Job M, arrival ω j < t → j ∈ F := fun j hj => (hfin t).mem_toFinset.2 hj.le
  have hJ : ((c, n) : Job M) ∈ F := hF _ hTt
  unfold workG
  rw [workP_eq_sum ω _ F hF, workP_eq_sum ω _ F hF]
  have key : ∀ j ∈ F,
      Set.indicator {j : Job M | AH h c n j ∧ arrival ω (c, n) ≤ arrival ω j ∧ arrival ω j < t}
        (serviceReq ω) j =
      (if j = (c, n) then serviceReq ω (c, n) else 0) +
        Set.indicator {j : Job M | j.1 ∈ h ∧ arrival ω (c, n) ≤ arrival ω j ∧ arrival ω j < t}
          (serviceReq ω) j := by
    intro j _
    by_cases hjJ : j = (c, n)
    · subst hjJ
      simp [Set.indicator_apply, AH, hc_notin, hTt]
    · by_cases hjh : j.1 ∈ h
      · simp [Set.indicator_apply, AH, hjh, hjJ]
      · have hno : ¬ (AH h c n j ∧ arrival ω (c, n) ≤ arrival ω j ∧ arrival ω j < t) := by
          rintro ⟨(h1 | ⟨h1, h2⟩), h3, -⟩
          · exact hjh h1
          · have hlt : j.2 < n := lt_of_le_of_ne h2 (fun e => hjJ (Prod.ext h1 e))
            have h4 := hinc c j.2 n hlt
            have hj' : ((c, j.2) : Job M) = j := by rw [← h1]
            rw [hj'] at h4
            linarith
        rw [Set.indicator_of_notMem (show j ∉ {j : Job M | AH h c n j ∧
          arrival ω (c, n) ≤ arrival ω j ∧ arrival ω j < t} from hno),
          Set.indicator_of_notMem (show j ∉ {j : Job M | j.1 ∈ h ∧
          arrival ω (c, n) ≤ arrival ω j ∧ arrival ω j < t} from fun hc => hjh hc.1),
          if_neg hjJ]
        ring
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', hJ, if_true]

/-- Left-local constancy: a priority schedule is constant on some `(l, D)`. -/
theorem left_const {M : ℕ} (σ : Equiv.Perm (Fin M)) (S : Schedule M) (ω : Omega M)
    (hG : GoodAt S ω) (hP : PrioAt σ S ω) (D : ℝ) :
    ∃ l < D, ∀ s ∈ Set.Ioo l D, ∀ s' ∈ Set.Ioo l D, S ω s = S ω s' := by
  classical
  set F := (hG.1 D).toFinset
  have hev : ∀ j : Job M, ∃ p : Prop, ∀ᶠ s in 𝓝[<] D, (present S j ω s ↔ p) := by
    intro j
    by_cases ha : arrival ω j < D
    · by_cases hd : ∃ s0 < D, serviceReq ω j ≤ served S j ω s0
      · obtain ⟨s0, hs0, hreq⟩ := hd
        refine ⟨False, ?_⟩
        filter_upwards [Ioo_mem_nhdsLT hs0] with s hs
        simp only [iff_false]
        rintro ⟨-, hlt⟩
        linarith [served_mono S j ω hs.1.le]
      · push_neg at hd
        refine ⟨True, ?_⟩
        filter_upwards [Ioo_mem_nhdsLT ha] with s hs
        simp only [iff_true]
        exact ⟨hs.1.le, hd s hs.2⟩
    · refine ⟨False, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [iff_false]
      rintro ⟨h1, -⟩
      exact ha (lt_of_le_of_lt h1 hs)
  choose p hp using hev
  have hall : ∀ᶠ s in 𝓝[<] D, ∀ j ∈ F, (present S j ω s ↔ p j) := by
    rw [Filter.eventually_all_finset]; exact fun j _ => hp j
  obtain ⟨l, hl, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hall
  refine ⟨l, hl, fun s hs s' hs' => sched_eq_of_present_iff σ S ω hG hP fun j => ?_⟩
  by_cases hjF : j ∈ F
  · have e1 : present S j ω s ↔ p j := hsub hs j hjF
    have e2 : present S j ω s' ↔ p j := hsub hs' j hjF
    rw [e1, e2]
  · have hnot : ∀ u < D, ¬ present S j ω u := by
      rintro u hu ⟨h1, -⟩
      exact hjF ((hG.1 D).mem_toFinset.2 (h1.trans hu.le))
    exact iff_of_false (hnot s hs.2) (hnot s' hs'.2)

theorem departure_facts {M : ℕ} (S : Schedule M) (ω : Omega M) (j : Job M)
    (hreq : 0 < serviceReq ω j) (hdone : ∃ t, serviceReq ω j ≤ served S j ω t) :
    serviceReq ω j ≤ served S j ω (departure S j ω) ∧
      ∀ t < departure S j ω, served S j ω t < serviceReq ω j := by
  unfold departure
  have hbdd : BddBelow {t : ℝ | serviceReq ω j ≤ served S j ω t} := ⟨0, fun t ht => by
    by_contra hc
    push_neg at hc
    have h0 := served_of_nonpos S j ω hc.le
    simp only [Set.mem_setOf_eq] at ht
    linarith⟩
  have hclosed : IsClosed {t : ℝ | serviceReq ω j ≤ served S j ω t} :=
    isClosed_le continuous_const (served_continuous S j ω)
  refine ⟨hclosed.csInf_mem hdone hbdd, fun t ht => ?_⟩
  by_contra hc
  push_neg at hc
  exact absurd (csInf_le hbdd hc) (not_le.2 ht)

/-- **C1e (pathwise response time).** -/
theorem response_eq_delayBP {M : ℕ} (σ : Equiv.Perm (Fin M)) (S : Schedule M) (ω : Omega M)
    (hG : GoodAt S ω) (hP : PrioAt σ S ω) (harr : ∀ j : Job M, 0 ≤ arrival ω j)
    (hreq : ∀ j : Job M, 0 < serviceReq ω j)
    (hinc : ∀ (i : Fin M) (m m' : ℕ), m < m' → arrival ω (i, m) < arrival ω (i, m'))
    (g h : Finset (Fin M)) (c : Fin M) (n : ℕ)
    (hg : ∀ i, i ∈ g ↔ σ.symm i ≤ σ.symm c) (hh : ∀ i, i ∈ h ↔ σ.symm i < σ.symm c)
    (hdone : ∃ t, serviceReq ω (c, n) ≤ served S (c, n) ω t) :
    responseTime S (c, n) ω =
      delayBP ω h (arrival ω (c, n)) (backlog ω g (arrival ω (c, n)) + serviceReq ω (c, n)) := by
  classical
  have hreq0 : ∀ j, 0 ≤ serviceReq ω j := fun j => (hreq j).le
  obtain ⟨hDmem, hDlt⟩ := departure_facts S ω (c, n) (hreq _) hdone
  have hJT : served S (c, n) ω (arrival ω (c, n)) = 0 :=
    served_eq_zero_of_le_arrival S ω hG.2.1 _ le_rfl
  have hTD : arrival ω (c, n) < departure S (c, n) ω := by
    by_contra hc
    push_neg at hc
    have := served_mono S (c, n) ω hc
    linarith [hreq (c, n)]
  have hT0 : 0 ≤ arrival ω (c, n) := harr _
  have hgup : ∀ i i' : Fin M, i' ∈ g → σ.symm i < σ.symm i' → i ∈ g := by
    intro i i' hi' hlt
    rw [hg] at hi' ⊢
    exact hlt.le.trans hi'
  have hR0 : remP S ω (AH h c n) (arrival ω (c, n)) = backlog ω g (arrival ω (c, n)) := by
    rw [backlog_eq_remP σ S ω hG hP harr hreq0 g hgup hT0]
    exact remP_AH_T σ S ω hG harr hinc g h c n hg hh
  have hJA : AH h c n (c, n) := Or.inr ⟨rfl, le_rfl⟩
  have hbusy : ∀ u ∈ Set.Ico (arrival ω (c, n)) (departure S (c, n) ω),
      ∃ j, AH h c n j ∧ S ω u = some j := fun u hu =>
    serves_upclosed σ S ω hG hP (upClosed_AH σ h c n hh) hJA ⟨hu.1, hDlt u hu.2⟩
  have hform : ∀ t, arrival ω (c, n) < t → t ≤ departure S (c, n) ω →
      remP S ω (AH h c n) t = backlog ω g (arrival ω (c, n)) + serviceReq ω (c, n) +
        workG ω h (arrival ω (c, n)) t - (t - arrival ω (c, n)) := by
    intro t hTt htD
    rw [remP_accounting S ω hG.1 _ hT0 hTt.le, workP_AH σ ω hG.1 hinc h c n hh hTt,
      servP_busy σ S ω hG hP _ hT0 hTt.le
        (fun u hu => hbusy u ⟨hu.1, lt_of_lt_of_le hu.2 htD⟩), hR0]
    ring
  have hRD : remP S ω (AH h c n) (departure S (c, n) ω) = 0 := by
    obtain ⟨l, hl, hconst⟩ := left_const σ S ω hG hP (departure S (c, n) ω)
    obtain ⟨s, hs1, hs2⟩ := exists_between (max_lt hl hTD)
    have hls : l < s := lt_of_le_of_lt (le_max_left _ _) hs1
    have hTs : arrival ω (c, n) < s := lt_of_le_of_lt (le_max_right _ _) hs1
    have hsJ : S ω s = some (c, n) := by
      by_contra hne
      have hid := served_idle S (c, n) ω hs2.le fun u hu e =>
        hne ((hconst s ⟨hls, hs2⟩ u ⟨hls.trans_le hu.1, hu.2⟩).trans e)
      linarith [hDlt s hs2]
    have hSJ : ∀ u ∈ Set.Ico s (departure S (c, n) ω), S ω u = some (c, n) := fun u hu =>
      (hconst u ⟨hls.trans_le hu.1, hu.2⟩ s ⟨hls, hs2⟩).trans hsJ
    have hs0 : 0 ≤ s := hT0.trans hTs.le
    have hserv := served_serving S (c, n) ω hs0 hs2.le hSJ
    have hsp := servP_busy σ S ω hG hP (AH h c n) hs0 hs2.le
      fun u hu => ⟨(c, n), hJA, hSJ u hu⟩
    have hw : workP ω (AH h c n) s (departure S (c, n) ω) = 0 := by
      unfold workP
      refine (tsum_congr fun j => Set.indicator_of_notMem ?_ _).trans tsum_zero
      rintro ⟨hjA, hjs, hjD⟩
      have hpr : present S j ω (arrival ω j) :=
        ⟨le_rfl, by rw [served_eq_zero_of_le_arrival S ω hG.2.1 j le_rfl]; exact hreq j⟩
      have e := only_J σ S ω hP h c n hh (hSJ _ ⟨hjs, hjD⟩) hjA hpr
      rw [e] at hjs
      linarith
    have hRs : remP S ω (AH h c n) s = serviceReq ω (c, n) - served S (c, n) ω s := by
      set F := (hG.1 s).toFinset
      have hF : ∀ j : Job M, arrival ω j < s → j ∈ F := fun j hj => (hG.1 s).mem_toFinset.2 hj.le
      rw [remP_eq_sum S ω hG harr _ F hF, Finset.sum_eq_single (c, n)]
      · rw [if_pos ⟨hJA, hTs⟩]
      · intro j _ hjJ
        split_ifs with hc
        · obtain ⟨hjA, hjs⟩ := hc
          have hge : serviceReq ω j ≤ served S j ω s := by
            by_contra hlt
            push_neg at hlt
            exact hjJ (only_J σ S ω hP h c n hh hsJ hjA ⟨hjs.le, hlt⟩)
          linarith [served_le_req S ω hG.2.1 j (hreq0 j) s]
        · rfl
      · intro hJF
        exact absurd (hF _ hTs) hJF
    rw [remP_accounting S ω hG.1 _ hs0 hs2.le, hRs, hw, hsp]
    linarith [served_le_req S ω hG.2.1 (c, n) (hreq0 _) (departure S (c, n) ω)]
  have hset : IsLeast {u : ℝ | 0 ≤ u ∧ backlog ω g (arrival ω (c, n)) + serviceReq ω (c, n) +
      workG ω h (arrival ω (c, n)) (arrival ω (c, n) + u) ≤ u}
      (departure S (c, n) ω - arrival ω (c, n)) := by
    refine ⟨⟨by linarith, ?_⟩, fun u hu => ?_⟩
    · have e := hform _ hTD le_rfl
      rw [hRD] at e
      rw [show arrival ω (c, n) + (departure S (c, n) ω - arrival ω (c, n)) =
        departure S (c, n) ω by ring]
      linarith
    · by_contra hlt
      push_neg at hlt
      rcases hu.1.lt_or_eq with hpos | hzero
      · have h1 := hform (arrival ω (c, n) + u) (by linarith) (by linarith)
        have h2 := remP_ge_term S ω hG harr hreq0 (AH h c n) hJA
          (show arrival ω (c, n) < arrival ω (c, n) + u by linarith)
        have h3 := hDlt (arrival ω (c, n) + u) (by linarith)
        rw [h1] at h2
        linarith [hu.2]
      · have e := hu.2
        rw [← hzero, add_zero] at e
        unfold workG at e
        rw [workP_self] at e
        have hb : 0 ≤ backlog ω g (arrival ω (c, n)) := le_max_left _ _
        linarith [hreq (c, n)]
  unfold responseTime delayBP
  rw [hset.csInf_eq]


theorem mem_erase_iff_of {M : ℕ} (σ : Equiv.Perm (Fin M)) (k : Fin M) (g : Finset (Fin M))
    (hg : ∀ i, i ∈ g ↔ σ.symm i ≤ k) (i : Fin M) :
    i ∈ g.erase (σ k) ↔ σ.symm i < σ.symm (σ k) := by
  rw [Finset.mem_erase, hg, Equiv.symm_apply_apply]
  constructor
  · rintro ⟨hne, hle⟩
    exact lt_of_le_of_ne hle (fun e => hne (by rw [← e]; simp))
  · intro h
    exact ⟨fun e => by rw [e, Equiv.symm_apply_apply] at h; exact lt_irrefl _ h, h.le⟩

/-- Pathwise clauses 2-4 of `IsStrategy` (what the pathwise child needs). -/
def PathStrategy (D : Data) (S : Schedule D.M) : Prop :=
  ∀ᵐ ω ∂D.P, (∀ (t : ℝ) (j : Job D.M), S ω t = some j → present S j ω t) ∧
    (∀ t : ℝ, S ω t = none ↔ ∀ j : Job D.M, ¬ present S j ω t) ∧
    (∀ j : Job D.M, ∃ t : ℝ, serviceReq ω j ≤ served S j ω t)

/-- **C1 (pathwise response time, almost surely).** -/
theorem C1_pathwise (D : Data) (σ : Equiv.Perm (Fin D.M)) (S : Schedule D.M)
    (hP : IsPriority D σ S) (hS : PathStrategy D S) (k : Fin D.M) (g : Finset (Fin D.M))
    (hg : ∀ i, i ∈ g ↔ σ.symm i ≤ k) :
    ∀ᵐ ω ∂D.P, ∀ n : ℕ, responseTime S (σ k, n) ω =
      delayBP ω (g.erase (σ k)) (arrival ω (σ k, n))
        (backlog ω g (arrival ω (σ k, n)) + serviceReq ω (σ k, n)) := by
  filter_upwards [hP, hS, ae_interarrival_pos D, ae_service_pos D, ae_arrival_finite D]
    with ω hPω hSω hia hsv hfin n
  obtain ⟨h2, h3, h4⟩ := hSω
  have hG : GoodAt S ω := ⟨hfin, h2, h3⟩
  have harr : ∀ j : Job D.M, 0 ≤ arrival ω j := fun j => by
    unfold arrival
    exact Finset.sum_nonneg fun m _ => (hia _).le
  have hg' : ∀ i, i ∈ g ↔ σ.symm i ≤ σ.symm (σ k) := fun i => by
    rw [Equiv.symm_apply_apply]; exact hg i
  exact response_eq_delayBP σ S ω hG hPω harr hsv
    (fun i m m' h => arrival_lt_of_lt ω hia i h) _ _ (σ k) n hg'
    (mem_erase_iff_of σ k g hg) (h4 _)


/-! ### C1 on the platform `chain` -/

theorem mem_chain_iff {M : ℕ} (σ : Equiv.Perm (Fin M)) (k i : Fin M) :
    i ∈ chain σ k ↔ σ.symm i ≤ k := by
  unfold chain
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa using ha
  · intro h
    exact ⟨σ.symm i, h, by simp⟩

theorem C1_chain (D : Data) (σ : Equiv.Perm (Fin D.M)) (S : Schedule D.M)
    (hP : IsPriority D σ S) (hS : PathStrategy D S) (k : Fin D.M) :
    ∀ᵐ ω ∂D.P, ∀ n : ℕ, responseTime S (σ k, n) ω =
      delayBP ω ((chain σ k).erase (σ k)) (arrival ω (σ k, n))
        (backlog ω (chain σ k) (arrival ω (σ k, n)) + serviceReq ω (σ k, n)) :=
  C1_pathwise D σ S hP hS k (chain σ k) (mem_chain_iff σ k)

end CM4




namespace CM4

open CoffmanMitrani

theorem rho_pos (D : Data) (i : Fin D.M) : 0 < D.rho i := by
  unfold Data.rho
  exact div_pos (D.lam_pos i) (D.mu_pos i)

theorem chain_zero {M : ℕ} (σ : Equiv.Perm (Fin M)) (k : Fin M) (hk : k.val = 0) :
    chain σ k = {σ k} := by
  ext a
  simp only [chain, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · rintro ⟨l, hl, rfl⟩
    have hlk : l = k := by
      apply Fin.ext
      rw [Fin.le_iff_val_le_val] at hl
      omega
    rw [hlk]
  · rintro rfl
    exact ⟨k, le_refl _, rfl⟩

theorem chain_succ {M : ℕ} (σ : Equiv.Perm (Fin M)) (k k' : Fin M) (hk : k'.val + 1 = k.val) :
    chain σ k = insert (σ k) (chain σ k') ∧ σ k ∉ chain σ k' := by
  constructor
  · ext a
    simp only [chain, Finset.mem_insert, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨l, hl, rfl⟩
      by_cases h : l = k
      · left
        rw [h]
      · right
        refine ⟨l, ?_, rfl⟩
        have hne : l.val ≠ k.val := fun e => h (Fin.ext e)
        rw [Fin.le_iff_val_le_val] at hl ⊢
        omega
    · rintro (rfl | ⟨l, hl, rfl⟩)
      · exact ⟨k, le_refl _, rfl⟩
      · refine ⟨l, ?_, rfl⟩
        rw [Fin.le_iff_val_le_val] at hl ⊢
        omega
  · simp only [chain, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, not_exists,
      not_and]
    intro l hl he
    have hlk := σ.injective he
    subst hlk
    rw [Fin.le_iff_val_le_val] at hl
    omega

theorem chain_unique (D : Data) (σ : Equiv.Perm (Fin D.M)) (W W' : Fin D.M → ℝ)
    (h1 : ∀ k, ∑ i ∈ chain σ k, D.rho i * W i = D.loadBound (chain σ k))
    (h2 : ∀ k, ∑ i ∈ chain σ k, D.rho i * W' i = D.loadBound (chain σ k)) : W = W' := by
  have hpt : ∀ k : Fin D.M, D.rho (σ k) * W (σ k) = D.rho (σ k) * W' (σ k) := by
    intro k
    by_cases hk : k.val = 0
    · have e := chain_zero σ k hk
      have a1 := h1 k
      have a2 := h2 k
      rw [e, Finset.sum_singleton] at a1 a2
      rw [a1, a2]
    · let k' : Fin D.M := ⟨k.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩
      have hk' : k'.val + 1 = k.val := by
        show k.val - 1 + 1 = k.val
        omega
      obtain ⟨e, hn⟩ := chain_succ σ k k' hk'
      have a1 := h1 k
      have a2 := h2 k
      have b1 := h1 k'
      have b2 := h2 k'
      rw [e, Finset.sum_insert hn] at a1 a2
      linarith
  funext i
  have h := hpt (σ.symm i)
  rw [Equiv.apply_symm_apply] at h
  exact mul_left_cancel₀ (ne_of_gt (rho_pos D i)) h


/-- Pure algebra of the inductive step: `L' + r * (L + 1/μ)/(1 - s) = L`. -/
theorem alg_step (R s r mu : ℝ) (hmu : mu ≠ 0) (h1 : 1 - s ≠ 0) (h2 : 1 - (r + s) ≠ 0) :
    r * (((r / mu + R) / (1 - (r + s)) + 1 / mu) / (1 - s)) + R / (1 - s) =
      (r / mu + R) / (1 - (r + s)) := by
  field_simp
  ring

theorem sum_rho_lt_one (D : Data) (g : Finset (Fin D.M)) : ∑ i ∈ g, D.rho i < 1 := by
  have hle : ∑ i ∈ g, D.rho i ≤ ∑ i, D.rho i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ g)
      (fun i _ _ => le_of_lt (rho_pos D i))
  have ht : ∑ i, D.rho i < 1 := by
    simpa [Data.rho] using D.stable
  linarith

/-- **Assembly from the preemptive-priority class formula.** If every class `σ k` has the classical
mean response time `(L_k + 1/μ_{σk}) / (1 - ρ_{<k})` (Cobham 1954; Kleinrock, Queueing Systems II, §3.7,
exponential service: `R_k = Σ_{i ≤ k} λ_i E X_i²/2 = Σ ρ_i/μ_i`, `L_k = R_k/(1-ρ_{≤k})`), then `W` solves
the chain equations (5). -/
theorem chain_eq_of_formula (D : Data) (σ : Equiv.Perm (Fin D.M)) (W : Fin D.M → ℝ)
    (hf : ∀ k : Fin D.M, W (σ k) =
      (D.loadBound (chain σ k) + 1 / D.mu (σ k)) / (1 - ∑ i ∈ (chain σ k).erase (σ k), D.rho i)) :
    ∀ k : Fin D.M, ∑ i ∈ chain σ k, D.rho i * W i = D.loadBound (chain σ k) := by
  have key : ∀ n : ℕ, ∀ k : Fin D.M, k.val = n →
      ∑ i ∈ chain σ k, D.rho i * W i = D.loadBound (chain σ k) := by
    intro n
    induction n with
    | zero =>
      intro k hk
      have e := chain_zero σ k hk
      have hw := hf k
      rw [e, Finset.erase_singleton, Finset.sum_empty] at hw
      rw [e, Finset.sum_singleton, hw]
      have hmu : D.mu (σ k) ≠ 0 := ne_of_gt (D.mu_pos _)
      have h2 : 1 - (D.rho (σ k) + 0) ≠ 0 := by
        have := sum_rho_lt_one D {σ k}
        rw [Finset.sum_singleton] at this
        intro h; linarith
      have hs : (1 : ℝ) - 0 ≠ 0 := by norm_num
      have := alg_step 0 0 (D.rho (σ k)) (D.mu (σ k)) hmu hs h2
      simp only [Data.loadBound, Finset.sum_singleton]
      simp only [add_zero, sub_zero, div_one] at this ⊢
      linarith
    | succ n ih =>
      intro k hk
      let k' : Fin D.M := ⟨n, by omega⟩
      have hk' : k'.val + 1 = k.val := by simp [k', hk]
      obtain ⟨e, hn⟩ := chain_succ σ k k' hk'
      have hw := hf k
      rw [e, Finset.erase_insert hn] at hw
      have hprev := ih k' rfl
      rw [e, Finset.sum_insert hn, hprev, hw]
      have hmu : D.mu (σ k) ≠ 0 := ne_of_gt (D.mu_pos _)
      have h1 : 1 - ∑ i ∈ chain σ k', D.rho i ≠ 0 := by
        have := sum_rho_lt_one D (chain σ k'); intro h; linarith
      have h2 : 1 - (D.rho (σ k) + ∑ i ∈ chain σ k', D.rho i) ≠ 0 := by
        have := sum_rho_lt_one D (insert (σ k) (chain σ k'))
        rw [Finset.sum_insert hn] at this
        intro h; linarith
      have := alg_step (∑ i ∈ chain σ k', D.rho i / D.mu i) (∑ i ∈ chain σ k', D.rho i)
        (D.rho (σ k)) (D.mu (σ k)) hmu h1 h2
      simp only [Data.loadBound, Finset.sum_insert hn]
      exact this
  intro k
  exact key k.val k rfl

end CM4

namespace CM4
open CoffmanMitrani MeasureTheory

/-- **Parent from C2 + C3.** C1 (proved) + C2 + C3 give the class formula; `chain_eq_of_formula`
gives existence and `chain_unique` uniqueness. -/
theorem chain_solution_of_C2_C3 (D : Data) (σ : Equiv.Perm (Fin D.M)) (S : Schedule D.M)
    (W : Fin D.M → ℝ) (hP : IsPriority D σ S) (hS : PathStrategy D S) (hW : Achieves D S W)
    (hC2 : ∀ (k : Fin D.M) (n : ℕ),
      ∫ ω, delayBP ω ((chain σ k).erase (σ k)) (arrival ω (σ k, n))
        (backlog ω (chain σ k) (arrival ω (σ k, n)) + serviceReq ω (σ k, n)) ∂D.P =
      ((∫ ω, backlog ω (chain σ k) (arrival ω (σ k, n)) ∂D.P) + 1 / D.mu (σ k)) /
        (1 - ∑ i ∈ (chain σ k).erase (σ k), D.rho i))
    (hC3 : ∀ k : Fin D.M, Filter.Tendsto
      (fun n : ℕ => ∫ ω, backlog ω (chain σ k) (arrival ω (σ k, n)) ∂D.P)
      Filter.atTop (nhds (D.loadBound (chain σ k))))
    (W' : Fin D.M → ℝ) :
    (∀ k : Fin D.M, ∑ i ∈ chain σ k, D.rho i * W' i = D.loadBound (chain σ k)) ↔ W' = W := by
  have hf : ∀ k : Fin D.M, W (σ k) =
      (D.loadBound (chain σ k) + 1 / D.mu (σ k)) /
        (1 - ∑ i ∈ (chain σ k).erase (σ k), D.rho i) := by
    intro k
    have hlim := (hW (σ k)).2
    have heq : (fun n : ℕ => ∫ ω, responseTime S (σ k, n) ω ∂D.P) =
        fun n => ((∫ ω, backlog ω (chain σ k) (arrival ω (σ k, n)) ∂D.P) + 1 / D.mu (σ k)) /
          (1 - ∑ i ∈ (chain σ k).erase (σ k), D.rho i) := by
      funext n
      rw [← hC2 k n]
      apply integral_congr_ae
      filter_upwards [C1_chain D σ S hP hS k] with ω hω
      exact hω n
    rw [heq] at hlim
    have h2 := ((hC3 k).add_const (1 / D.mu (σ k))).div_const
      (1 - ∑ i ∈ (chain σ k).erase (σ k), D.rho i)
    exact tendsto_nhds_unique hlim h2
  have hex := chain_eq_of_formula D σ W hf
  constructor
  · intro h
    exact (chain_unique D σ W W' hex h).symm
  · rintro rfl
    exact hex

end CM4

/-! 608dae3b relay 19: final assembly (C1 + C2 + C3 -> chain_solution). -/
namespace CM4F
open CoffmanMitrani MeasureTheory Filter Topology

theorem conv (D : Data) (σ : Equiv.Perm (Fin D.M)) (S : Schedule D.M)
    (W : Fin D.M → ℝ) (hP : IsPriority D σ S) (hS : CM4.PathStrategy D S) (hW : Achieves D S W)
    (hC2 : ∀ (k : Fin D.M) (n : ℕ),
      ∫ ω, CM4.delayBP ω ((chain σ k).erase (σ k)) (arrival ω (σ k, n))
        (CM4.backlog ω (chain σ k) (arrival ω (σ k, n)) + serviceReq ω (σ k, n)) ∂D.P =
      ((∫ ω, CM4.backlog ω (chain σ k) (arrival ω (σ k, n)) ∂D.P) + 1 / D.mu (σ k)) /
        (1 - ∑ i ∈ (chain σ k).erase (σ k), D.rho i))
    (k : Fin D.M) (hd : 1 - ∑ i ∈ (chain σ k).erase (σ k), D.rho i ≠ 0) :
    Tendsto (fun n : ℕ => ∫ ω, CM4.backlog ω (chain σ k) (arrival ω (σ k, n)) ∂D.P) atTop
      (nhds (W (σ k) * (1 - ∑ i ∈ (chain σ k).erase (σ k), D.rho i) - 1 / D.mu (σ k))) := by
  have hlim := (hW (σ k)).2
  have heq : (fun n : ℕ => ∫ ω, responseTime S (σ k, n) ω ∂D.P) =
      fun n => ((∫ ω, CM4.backlog ω (chain σ k) (arrival ω (σ k, n)) ∂D.P) + 1 / D.mu (σ k)) /
        (1 - ∑ i ∈ (chain σ k).erase (σ k), D.rho i) := by
    funext n
    rw [← hC2 k n]
    apply integral_congr_ae
    filter_upwards [CM4.C1_chain D σ S hP hS k] with ω hω
    exact hω n
  rw [heq] at hlim
  have h2 := (hlim.mul_const (1 - ∑ i ∈ (chain σ k).erase (σ k), D.rho i)).sub_const
    (1 / D.mu (σ k))
  refine h2.congr' (Eventually.of_forall fun n => ?_)
  simp only
  rw [div_mul_cancel₀ _ hd]
  ring

end CM4F

end CM4B

open CoffmanMitrani in
theorem solution (D : Data) (σ : Equiv.Perm (Fin D.M)) (S : Schedule D.M)
    (W : Fin D.M → ℝ) (hP : IsPriority D σ S) (hS : IsStrategy D S) (hW : Achieves D S W)
    (W' : Fin D.M → ℝ) :
    (∀ k : Fin D.M, ∑ i ∈ chain σ k, D.rho i * W' i = D.loadBound (chain σ k)) ↔
      W' = W := by
  have hPS : CM4B.CM4.PathStrategy D S := by
    obtain ⟨_, rule, h⟩ := hS
    exact h.mono fun ω hω => ⟨hω.1, hω.2.1, hω.2.2.1⟩
  have hmem : ∀ k, σ k ∈ chain σ k := fun k =>
    Finset.mem_image.2 ⟨k, by simp, rfl⟩
  have hnn : ∀ i, 0 ≤ D.lam i / D.mu i := fun i => (div_pos (D.lam_pos i) (D.mu_pos i)).le
  have hlt : ∀ k, ∑ i ∈ chain σ k, D.lam i / D.mu i < 1 := fun k =>
    lt_of_le_of_lt (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun i _ _ => hnn i) D.stable
  have hd : ∀ k, 1 - ∑ i ∈ (chain σ k).erase (σ k), D.rho i ≠ 0 := by
    intro k
    have h1 : ∑ i ∈ (chain σ k).erase (σ k), D.rho i ≤ ∑ i ∈ chain σ k, D.lam i / D.mu i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun i _ _ => hnn i
    have h2 := hlt k
    intro h
    linarith
  have hC2 : ∀ (k : Fin D.M) (n : ℕ),
      ∫ ω, CM4B.CM4.delayBP ω ((chain σ k).erase (σ k)) (arrival ω (σ k, n))
        (CM4B.CM4.backlog ω (chain σ k) (arrival ω (σ k, n)) + serviceReq ω (σ k, n)) ∂D.P =
      ((∫ ω, CM4B.CM4.backlog ω (chain σ k) (arrival ω (σ k, n)) ∂D.P) + 1 / D.mu (σ k)) /
        (1 - ∑ i ∈ (chain σ k).erase (σ k), D.rho i) := fun k n =>
    CM4B.CM4G.C2_exact D (chain σ k) (σ k) n
  have hC3 : ∀ k : Fin D.M, Filter.Tendsto
      (fun n : ℕ => ∫ ω, CM4B.CM4.backlog ω (chain σ k) (arrival ω (σ k, n)) ∂D.P)
      Filter.atTop (nhds (D.loadBound (chain σ k))) := by
    intro k
    have ht := CM4B.CM4F.conv D σ S W hP hPS hW hC2 k (hd k)
    have hL := CM4B.CM4S12.C3_limit D (chain σ k) (σ k) (hmem k) (hlt k) _ ht
    have hb : D.loadBound (chain σ k) = (∑ i ∈ chain σ k, D.lam i / D.mu i ^ 2) /
        (1 - ∑ i ∈ chain σ k, D.lam i / D.mu i) := by
      unfold Data.loadBound Data.rho
      congr 1
      exact Finset.sum_congr rfl fun i _ => by rw [div_div, pow_two]
    rw [hb, ← hL]
    exact ht
  exact CM4B.CM4.chain_solution_of_C2_C3 D σ S W hP hPS hW hC2 hC3 W'
