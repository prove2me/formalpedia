-- Prove2me | solution 1 for GIGnBounds.Tail.theorem_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-25T00:29:59.328033+00:00
-- url     : https://prove2.me/submissions/bdbb9ad6-d235-487b-8327-d140ee1e2b3f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_GIGnBounds_Tail_Setting
import Theorems.Thm_GIGnBounds_Tail_lemma_1
import Theorems.Thm_GIGnBounds_Tail_lemma_7
import Theorems.Thm_GIGnBounds_Tail_sup_bound_r_gt_2_5

open MeasureTheory ProbabilityTheory GIGnBounds.Tail Filter Topology


namespace GIGnGoalAux

/-- The equilibrium law of a time law is a probability measure (layer-cake formula). -/
lemma eqLaw_isProb (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : IsTimeLaw μ) :
    IsProbabilityMeasure (eqLaw μ) := by
  constructor
  have hrate : 0 < rate μ := inv_pos.mpr hμ.mean_pos
  have hae : ∀ᵐ x ∂μ, 0 ≤ x := by
    have hs : {a : ℝ | ¬ 0 ≤ a} = Set.Iio 0 := by ext; simp
    rw [ae_iff, hs]; exact hμ.nonneg
  rw [eqLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have h1 : ∀ z, ENNReal.ofReal (rate μ * (μ (Set.Ioi z)).toReal) =
      ENNReal.ofReal (rate μ) * μ (Set.Ioi z) := by
    intro z
    rw [ENNReal.ofReal_mul hrate.le, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  simp_rw [h1]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hlc := lintegral_eq_lintegral_meas_lt μ hae aemeasurable_id
  try simp only [id_eq, id] at hlc
  have : ∫⁻ t in Set.Ioi 0, μ (Set.Ioi t) = ∫⁻ t in Set.Ioi 0, μ {a : ℝ | t < a} := rfl
  rw [this, ← hlc, ← ofReal_integral_eq_lintegral_ofReal hμ.integrable hae,
    ← ENNReal.ofReal_mul hrate.le]
  have : rate μ * ∫ x, x ∂μ = 1 := by
    rw [rate, mean]; exact inv_mul_cancel₀ hμ.mean_pos.ne'
  rw [this, ENNReal.ofReal_one]

/-- The index type of all renewal intervals of a bounding family. -/
abbrev Idx (m : ℕ) : Type := Option ℕ ⊕ (Fin m × Option ℕ)

/-- The law of each interval of the bounding family. -/
noncomputable def lawIdx (m : ℕ) (μA μS : Measure ℝ) : Idx m → Measure ℝ
  | Sum.inl none => eqLaw μA
  | Sum.inl (some _) => μA
  | Sum.inr (_, none) => eqLaw μS
  | Sum.inr (_, some _) => μS

lemma lawIdx_isProb (m : ℕ) (μA μS : Measure ℝ) [IsProbabilityMeasure μA]
    [IsProbabilityMeasure μS] (hA : IsTimeLaw μA) (hS : IsTimeLaw μS) (k : Idx m) :
    IsProbabilityMeasure (lawIdx m μA μS k) := by
  rcases k with (_ | _) | ⟨_, _ | _⟩
  · exact eqLaw_isProb μA hA
  · simp only [lawIdx]; infer_instance
  · exact eqLaw_isProb μS hS
  · simp only [lawIdx]; infer_instance

/-- The product probability space carrying all renewal intervals. -/
noncomputable def canonP (m : ℕ) (μA μS : Measure ℝ) [IsProbabilityMeasure μA]
    [IsProbabilityMeasure μS] (hA : IsTimeLaw μA) (hS : IsTimeLaw μS) : Measure (Idx m → ℝ) :=
  haveI := lawIdx_isProb m μA μS hA hS
  Measure.infinitePi (lawIdx m μA μS)

instance canonP_isProb (m : ℕ) (μA μS : Measure ℝ) [IsProbabilityMeasure μA]
    [IsProbabilityMeasure μS] (hA : IsTimeLaw μA) (hS : IsTimeLaw μS) :
    IsProbabilityMeasure (canonP m μA μS hA hS) := by
  haveI := lawIdx_isProb m μA μS hA hS
  unfold canonP; infer_instance

/-- Existence of the bounding family `{𝒩_{e,i}} ∪ {𝒜_e}` on a product probability space. -/
noncomputable def canonFamily (m : ℕ) (μA μS : Measure ℝ) [IsProbabilityMeasure μA]
    [IsProbabilityMeasure μS] (hA : IsTimeLaw μA) (hS : IsTimeLaw μS) :
    RenewalFamily (Idx m → ℝ) (canonP m μA μS hA hS) m μA μS :=
  haveI := lawIdx_isProb m μA μS hA hS
  { srv := fun i j ω => ω (Sum.inr (i, j))
    measurable_srv := fun i j => measurable_pi_apply _
    law_srv_none := fun i => by
      unfold canonP; rw [Measure.infinitePi_map_eval]; rfl
    law_srv_some := fun i j => by
      unfold canonP; rw [Measure.infinitePi_map_eval]; rfl
    indep_srv := by
      have h := iIndepFun_infinitePi (P := lawIdx m μA μS) (X := fun _ x => x)
        (fun _ => measurable_id)
      have hinj : Function.Injective (fun p : Fin m × Option ℕ => (Sum.inr p : Idx m)) := by
        intro a b h; simpa using h
      unfold canonP
      exact h.precomp hinj
    arr := fun j ω => ω (Sum.inl j)
    measurable_arr := fun j => measurable_pi_apply _
    law_arr_none := by
      unfold canonP; rw [Measure.infinitePi_map_eval]; rfl
    law_arr_some := fun j => by
      unfold canonP; rw [Measure.infinitePi_map_eval]; rfl
    indep_all := by
      have h := iIndepFun_infinitePi (P := lawIdx m μA μS) (X := fun _ x => x)
        (fun _ => measurable_id)
      unfold canonP
      convert h using 2 with k
      ext ω
      rcases k with j | ⟨i, j⟩ <;> rfl }

end GIGnGoalAux



namespace GIGnGoalAux

/-- Scaling map `x ↦ c x`. -/
lemma meas_mul (c : ℝ) : Measurable (fun x : ℝ => c * x) := measurable_const.mul measurable_id

lemma mean_map (μ : Measure ℝ) (hμ : IsTimeLaw μ) (c : ℝ) :
    mean (μ.map (fun x => c * x)) = c * mean μ := by
  rw [mean, integral_map (f := fun x : ℝ => x) (meas_mul c).aemeasurable
    aestronglyMeasurable_id, mean]
  rw [integral_const_mul]

lemma rate_map (μ : Measure ℝ) (hμ : IsTimeLaw μ) (c : ℝ) :
    rate (μ.map (fun x => c * x)) = c⁻¹ * rate μ := by
  rw [rate, mean_map μ hμ c, rate, mul_inv]

lemma map_Ioi (μ : Measure ℝ) (c : ℝ) (hc : 0 < c) (w : ℝ) :
    (μ.map (fun x => c * x)) (Set.Ioi w) = μ (Set.Ioi (w / c)) := by
  rw [Measure.map_apply (meas_mul c) measurableSet_Ioi]
  congr 1
  ext z
  simp only [Set.mem_preimage, Set.mem_Ioi]
  rw [div_lt_iff₀ hc, mul_comm]

/-- The density of the equilibrium law, as a function. -/
noncomputable def eqDens (μ : Measure ℝ) (z : ℝ) : ENNReal :=
  ENNReal.ofReal (rate μ * (μ (Set.Ioi z)).toReal)

lemma eqDens_meas (μ : Measure ℝ) [IsFiniteMeasure μ] : Measurable (eqDens μ) := by
  unfold eqDens
  apply ENNReal.measurable_ofReal.comp
  apply Measurable.const_mul
  apply ENNReal.measurable_toReal.comp
  apply Antitone.measurable
  intro a b hab
  exact measure_mono (Set.Ioi_subset_Ioi hab)

/-- Scaling commutes with taking the equilibrium law. -/
lemma eqLaw_map (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : IsTimeLaw μ) (c : ℝ)
    (hc : 0 < c) : eqLaw (μ.map (fun x => c * x)) = (eqLaw μ).map (fun x => c * x) := by
  have hdens : ∀ w, eqDens (μ.map (fun x => c * x)) w =
      ENNReal.ofReal c⁻¹ * eqDens μ (w / c) := by
    intro w
    unfold eqDens
    rw [rate_map μ hμ c, map_Ioi μ c hc w, ← ENNReal.ofReal_mul (by positivity)]
    ring_nf
  ext s hs
  -- left side
  have hL : eqLaw (μ.map (fun x => c * x)) s =
      ∫⁻ w, (s ∩ Set.Ioi 0).indicator (eqDens (μ.map (fun x => c * x))) w := by
    rw [eqLaw, withDensity_apply _ hs, Measure.restrict_restrict hs,
      lintegral_indicator (hs.inter measurableSet_Ioi)]
    rfl
  -- right side
  set h : ℝ → ENNReal := (s ∩ Set.Ioi 0).indicator (fun w => eqDens μ (w / c)) with hh
  have hhm : Measurable h :=
    ((eqDens_meas μ).comp (measurable_id.div_const c)).indicator (hs.inter measurableSet_Ioi)
  have hR : (eqLaw μ).map (fun x => c * x) s = ∫⁻ z, h (c * z) := by
    rw [Measure.map_apply (meas_mul c) hs, eqLaw, withDensity_apply _ ((meas_mul c) hs),
      Measure.restrict_restrict ((meas_mul c) hs)]
    rw [← lintegral_indicator (((meas_mul c) hs).inter measurableSet_Ioi)]
    apply lintegral_congr
    intro z
    by_cases h1 : c * z ∈ s ∧ 0 < z
    · have hm1 : z ∈ (fun x => c * x) ⁻¹' s ∩ Set.Ioi 0 := ⟨h1.1, h1.2⟩
      have hm2 : c * z ∈ s ∩ Set.Ioi 0 := ⟨h1.1, mul_pos hc h1.2⟩
      simp only [hh, Set.indicator, hm1, hm2, if_true]
      unfold eqDens
      congr 3
      field_simp
    · have hm1 : z ∉ (fun x => c * x) ⁻¹' s ∩ Set.Ioi 0 := fun h' => h1 ⟨h'.1, h'.2⟩
      have hm2 : c * z ∉ s ∩ Set.Ioi 0 := fun h' =>
        h1 ⟨h'.1, pos_of_mul_pos_right (Set.mem_Ioi.mp h'.2) hc.le⟩
      simp only [hh, Set.indicator, hm1, hm2, if_false]
  have hchg : ∫⁻ z, h (c * z) = ENNReal.ofReal c⁻¹ * ∫⁻ w, h w := by
    have := lintegral_map hhm (meas_mul c) (μ := volume)
    rw [← this, Real.map_volume_mul_left hc.ne', lintegral_smul_measure,
      abs_of_pos (inv_pos.mpr hc), smul_eq_mul]
  rw [hL, hR, hchg, ← lintegral_const_mul _ hhm]
  apply lintegral_congr
  intro w
  simp only [hh, Set.indicator]
  split_ifs
  · exact hdens w
  · simp

/-- The bounding family rescaled by `c > 0`. -/
noncomputable def scaleFamily {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {m : ℕ}
    {μA μS : Measure ℝ} [IsProbabilityMeasure μA] [IsProbabilityMeasure μS]
    (hA : IsTimeLaw μA) (hS : IsTimeLaw μS) (F : RenewalFamily Ω P m μA μS) (c : ℝ) (hc : 0 < c) :
    RenewalFamily Ω P m (μA.map (fun x => c * x)) (μS.map (fun x => c * x)) where
  srv := fun i j ω => c * F.srv i j ω
  measurable_srv := fun i j => (meas_mul c).comp (F.measurable_srv i j)
  law_srv_none := fun i => by
    rw [← Function.comp_def (fun x => c * x) (F.srv i none),
      ← Measure.map_map (meas_mul c) (F.measurable_srv i none), F.law_srv_none i,
      eqLaw_map μS hS c hc]
  law_srv_some := fun i j => by
    rw [← Function.comp_def (fun x => c * x) (F.srv i (some j)),
      ← Measure.map_map (meas_mul c) (F.measurable_srv i (some j)), F.law_srv_some i j]
  indep_srv := by
    have := F.indep_srv.comp (fun _ x => c * x) (fun _ => meas_mul c)
    exact this
  arr := fun j ω => c * F.arr j ω
  measurable_arr := fun j => (meas_mul c).comp (F.measurable_arr j)
  law_arr_none := by
    rw [← Function.comp_def (fun x => c * x) (F.arr none),
      ← Measure.map_map (meas_mul c) (F.measurable_arr none), F.law_arr_none,
      eqLaw_map μA hA c hc]
  law_arr_some := fun j => by
    rw [← Function.comp_def (fun x => c * x) (F.arr (some j)),
      ← Measure.map_map (meas_mul c) (F.measurable_arr (some j)), F.law_arr_some j]
  indep_all := by
    have h := F.indep_all.comp (fun _ x => c * x) (fun _ => meas_mul c)
    show iIndepFun (fun k ω => Sum.elim (fun j => c * F.arr j ω)
      (fun p : Fin m × Option ℕ => c * F.srv p.1 p.2 ω) k) P
    have e : (fun k ω => Sum.elim (fun j => c * F.arr j ω)
        (fun p : Fin m × Option ℕ => c * F.srv p.1 p.2 ω) k) =
        fun k => (fun x : ℝ => c * x) ∘ (fun ω => Sum.elim (fun j => F.arr j ω)
          (fun p : Fin m × Option ℕ => F.srv p.1 p.2 ω) k) := by
      funext k ω
      rcases k with j | p <;> rfl
    rw [e]
    exact h

lemma eqCount_scale (R : ℝ) (X : ℕ → ℝ) (c t : ℝ) (hc : 0 < c) :
    eqCount (c * R) (fun j => c * X j) t = eqCount R X (t / c) := by
  unfold eqCount
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro k
  rw [← Finset.mul_sum, ← mul_add, le_div_iff₀ hc, mul_comm]

lemma supFrom_scale (f : ℝ → ℝ) (c : ℝ) (hc : 0 < c) :
    supFrom (fun t => f (t / c)) = supFrom f := by
  unfold supFrom
  apply le_antisymm
  · apply iSup₂_le
    intro t ht
    exact le_iSup₂ (f := fun t (_ : 0 ≤ t) => (f t : EReal)) (t / c) (div_nonneg ht hc.le)
  · apply iSup₂_le
    intro t ht
    have := le_iSup₂ (f := fun t (_ : 0 ≤ t) => (f (t / c) : EReal)) (c * t)
      (mul_nonneg hc.le ht)
    rwa [mul_div_cancel_left₀ t hc.ne'] at this

lemma scale_sup {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {m : ℕ}
    {μA μS : Measure ℝ} [IsProbabilityMeasure μA] [IsProbabilityMeasure μS]
    (hA : IsTimeLaw μA) (hS : IsTimeLaw μS) (F : RenewalFamily Ω P m μA μS) (c : ℝ) (hc : 0 < c)
    (ω : Ω) :
    supFrom (fun t => ((scaleFamily hA hS F c hc).Ae ω t : ℝ) -
        ∑ i, ((scaleFamily hA hS F c hc).Ne i ω t : ℝ)) =
      supFrom (fun t => (F.Ae ω t : ℝ) - ∑ i, (F.Ne i ω t : ℝ)) := by
  rw [← supFrom_scale (fun t => (F.Ae ω t : ℝ) - ∑ i, (F.Ne i ω t : ℝ)) c hc]
  congr 1
  ext t
  simp only [RenewalFamily.Ae, RenewalFamily.Ne, ServiceFamily.Ne, scaleFamily]
  rw [eqCount_scale _ _ c t hc]
  congr 2
  funext i
  rw [eqCount_scale _ _ c t hc]

end GIGnGoalAux



namespace GIGnGoalAux

lemma ae_nonneg_of (μ : Measure ℝ) (h0 : μ (Set.Iio 0) = 0) : ∀ᵐ x ∂μ, 0 ≤ x := by
  have hs : {a : ℝ | ¬ 0 ≤ a} = Set.Iio 0 := by ext; simp
  rw [ae_iff, hs]; exact h0

lemma timeLaw_map (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : IsTimeLaw μ) (c : ℝ)
    (hc : 0 < c) : IsTimeLaw (μ.map (fun x => c * x)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Measure.map_apply (meas_mul c) measurableSet_Iio]
    have : (fun x => c * x) ⁻¹' Set.Iio 0 = Set.Iio 0 := by
      ext a; simp only [Set.mem_preimage, Set.mem_Iio]
      constructor
      · intro h; by_contra h'; push Not at h'; nlinarith
      · intro h; nlinarith
    rw [this]; exact hμ.nonneg
  · rw [integrable_map_measure (g := fun x : ℝ => x) aestronglyMeasurable_id
      (meas_mul c).aemeasurable]
    exact hμ.integrable.const_mul c
  · have := mean_map μ hμ c
    rw [mean] at this
    rw [this]; exact mul_pos hc hμ.mean_pos

lemma nMoment_map (μ : Measure ℝ) (hμ : IsTimeLaw μ) (c : ℝ) (hc : 0 < c) (p : ℝ) :
    nMoment (μ.map (fun x => c * x)) p = nMoment μ p := by
  rw [nMoment, integral_map (f := fun x : ℝ => (x * rate (μ.map (fun x => c * x))) ^ p)
    (meas_mul c).aemeasurable
    ((measurable_id.mul_const _).pow_const p).aestronglyMeasurable, nMoment, rate_map μ hμ c]
  congr 1; ext x
  congr 1
  field_simp

lemma rho_map (n : ℕ) (μA μS : Measure ℝ) (hA : IsTimeLaw μA) (hS : IsTimeLaw μS) (c : ℝ)
    (hc : 0 < c) : rho n (μA.map (fun x => c * x)) (μS.map (fun x => c * x)) = rho n μA μS := by
  rw [rho, rho, rate_map μA hA c, rate_map μS hS c]
  have : c⁻¹ ≠ 0 := inv_ne_zero hc.ne'
  field_simp

lemma int_rpow_map (μ : Measure ℝ) (_hμ : IsTimeLaw μ) (p : ℝ) :
    ∫ y, y ^ p ∂(μ.map (fun x => rate μ * x)) = nMoment μ p := by
  rw [integral_map (f := fun y : ℝ => y ^ p) (meas_mul _).aemeasurable
    (measurable_id.pow_const p).aestronglyMeasurable, nMoment]
  congr 1; ext x; rw [mul_comm]

lemma int_sq_map (μ : Measure ℝ) (hμ : IsTimeLaw μ) :
    ∫ y, y ^ 2 ∂(μ.map (fun x => rate μ * x)) = nMoment μ 2 := by
  rw [← int_rpow_map μ hμ 2]
  congr 1; ext y; rw [Real.rpow_two]

lemma mean_scaled (μ : Measure ℝ) (hμ : IsTimeLaw μ) :
    mean (μ.map (fun x => rate μ * x)) = 1 := by
  rw [mean_map μ hμ, rate]; exact inv_mul_cancel₀ hμ.mean_pos.ne'

lemma lint_rpow_map (μ : Measure ℝ) (hμ : IsTimeLaw μ) (c : ℝ) (hc : 0 < c) (p : ℝ) (hp : 0 ≤ p) :
    ∫⁻ x, ENNReal.ofReal (x ^ p) ∂(μ.map (fun x => c * x)) =
      ENNReal.ofReal (c ^ p) * ∫⁻ x, ENNReal.ofReal (x ^ p) ∂μ := by
  rw [lintegral_map (f := fun x : ℝ => ENNReal.ofReal (x ^ p))
    (ENNReal.measurable_ofReal.comp (measurable_id.pow_const p)) (meas_mul c),
    ← lintegral_const_mul (ENNReal.ofReal (c ^ p)) (f := fun x : ℝ => ENNReal.ofReal (x ^ p))
      (ENNReal.measurable_ofReal.comp (measurable_id.pow_const p))]
  apply lintegral_congr_ae
  filter_upwards [ae_nonneg_of μ hμ.nonneg] with x hx
  rw [Real.mul_rpow hc.le hx, ENNReal.ofReal_mul (Real.rpow_nonneg hc.le _)]

lemma lint_sq_map (μ : Measure ℝ) (hμ : IsTimeLaw μ) (c : ℝ) (hc : 0 < c)
    (h2 : ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂μ < ⊤) :
    ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂(μ.map (fun x => c * x)) < ⊤ := by
  have e : ∀ ν : Measure ℝ, ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂ν = ∫⁻ x, ENNReal.ofReal (x ^ (2 : ℝ)) ∂ν := by
    intro ν; congr 1; ext x; rw [Real.rpow_two]
  rw [e, lint_rpow_map μ hμ c hc 2 (by norm_num)]
  rw [e] at h2
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top h2

lemma rStar_map (μ : Measure ℝ) (hμ : IsTimeLaw μ) (c : ℝ) (hc : 0 < c) :
    rStar μ ≤ rStar (μ.map (fun x => c * x)) := by
  unfold rStar
  apply sSup_le_sSup
  apply Set.image_mono
  intro p ⟨hp0, hpf⟩
  refine ⟨hp0, ?_⟩
  rw [lint_rpow_map μ hμ c hc p hp0]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hpf

end GIGnGoalAux



namespace GIGnGoalAux

/-! ### Moments of a mean-one time law -/

lemma integrable_rpow (μ : Measure ℝ) [IsProbabilityMeasure μ] (h0 : μ (Set.Iio 0) = 0)
    (r : ℝ) (h : ∫⁻ x, ENNReal.ofReal (x ^ r) ∂μ < ⊤) : Integrable (fun x : ℝ => x ^ r) μ := by
  refine ⟨(measurable_id.pow_const r).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal ((ae_nonneg_of μ h0).mono (fun x hx => Real.rpow_nonneg hx r))]
  exact h

lemma rpow_le_one_add (x r r' : ℝ) (hx : 0 ≤ x) (hr : 0 ≤ r) (hrr : r ≤ r') :
    x ^ r ≤ 1 + x ^ r' := by
  rcases le_total x 1 with h1 | h1
  · have := Real.rpow_le_one hx h1 hr
    have := Real.rpow_nonneg hx r'
    linarith
  · have := Real.rpow_le_rpow_of_exponent_le h1 hrr
    linarith

lemma moment_fin (μ : Measure ℝ) [IsProbabilityMeasure μ] (h0 : μ (Set.Iio 0) = 0)
    (r r' : ℝ) (hr : 0 ≤ r) (hrr : r ≤ r') (h : ∫⁻ x, ENNReal.ofReal (x ^ r') ∂μ < ⊤) :
    ∫⁻ x, ENNReal.ofReal (x ^ r) ∂μ < ⊤ := by
  have hle : ∀ᵐ x ∂μ, ENNReal.ofReal (x ^ r) ≤ 1 + ENNReal.ofReal (x ^ r') := by
    filter_upwards [ae_nonneg_of μ h0] with x hx
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num) (Real.rpow_nonneg hx _)]
    exact ENNReal.ofReal_le_ofReal (rpow_le_one_add x r r' hx hr hrr)
  calc ∫⁻ x, ENNReal.ofReal (x ^ r) ∂μ ≤ ∫⁻ x, (1 + ENNReal.ofReal (x ^ r')) ∂μ :=
        lintegral_mono_ae hle
    _ = 1 + ∫⁻ x, ENNReal.ofReal (x ^ r') ∂μ := by
        rw [lintegral_add_left measurable_const]; simp
    _ < ⊤ := ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top, h⟩

/-- `E[Z^r] ≥ 1` for a nonnegative `Z` with `E Z = 1` and `r ≥ 1` (Bernoulli's inequality). -/
lemma one_le_moment (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : IsTimeLaw μ)
    (hmean : ∫ z, z ∂μ = 1) (r : ℝ) (hr : 1 ≤ r) (h : ∫⁻ x, ENNReal.ofReal (x ^ r) ∂μ < ⊤) :
    1 ≤ ∫ y, y ^ r ∂μ := by
  have hI1 : Integrable (fun z : ℝ => z) μ := hμ.integrable
  have hIr := integrable_rpow μ hμ.nonneg r h
  have i1 : Integrable (fun z : ℝ => r * (z - 1)) μ := (hI1.sub (integrable_const 1)).const_mul r
  have i2 : Integrable (fun z : ℝ => 1 + r * (z - 1)) μ := (integrable_const 1).add i1
  have h1 : ∫ z, (1 + r * (z - 1)) ∂μ ≤ ∫ z, z ^ r ∂μ := by
    apply integral_mono_ae i2 hIr
    filter_upwards [ae_nonneg_of μ hμ.nonneg] with z hz
    have := one_add_mul_self_le_rpow_one_add (s := z - 1) (by linarith) (p := r) hr
    simpa using this
  have ea : ∫ z, (1 + r * (z - 1)) ∂μ = ∫ z, (1 : ℝ) ∂μ + ∫ z, r * (z - 1) ∂μ :=
    integral_add (integrable_const 1) i1
  have eb : ∫ z, (z - 1) ∂μ = ∫ z, z ∂μ - ∫ z, (1 : ℝ) ∂μ :=
    integral_sub hI1 (integrable_const 1)
  rw [ea, integral_const_mul, eb, hmean] at h1
  simpa using h1

/-! ### Right-continuity of the moment `r ↦ E[Z^r]` -/

lemma moment_tendsto (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : IsTimeLaw μ) (a r₀ : ℝ)
    (ha : 0 < a) (har : a < r₀) (h : ∫⁻ x, ENNReal.ofReal (x ^ r₀) ∂μ < ⊤) :
    Tendsto (fun r => ∫ y, y ^ r ∂μ) (𝓝[>] a) (𝓝 (∫ y, y ^ a ∂μ)) := by
  have hev : ∀ᶠ r in 𝓝[>] a, r ∈ Set.Ioo a r₀ := Ioo_mem_nhdsGT har
  apply tendsto_integral_filter_of_dominated_convergence (fun y => 1 + y ^ r₀)
  · exact Eventually.of_forall (fun r => (measurable_id.pow_const r).aestronglyMeasurable)
  · filter_upwards [hev] with r hr
    filter_upwards [ae_nonneg_of μ hμ.nonneg] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hy r)]
    exact rpow_le_one_add y r r₀ hy (by linarith [hr.1]) hr.2.le
  · exact (integrable_const 1).add (integrable_rpow μ hμ.nonneg r₀ h)
  · filter_upwards [ae_nonneg_of μ hμ.nonneg] with y hy
    rcases hy.lt_or_eq with hy | hy
    · exact tendsto_nhdsWithin_of_tendsto_nhds
        ((Real.continuousAt_const_rpow hy.ne').tendsto)
    · rw [← hy, Real.zero_rpow ha.ne']
      apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with r hr
      rw [Real.zero_rpow (ne_of_gt (lt_trans ha hr))]

/-- Right-continuity of the explicit bound in `r`. -/
lemma bound_tendsto (m K y G : ℝ) (N : ℝ → ℝ) (hm : 0 < m) (hK : 0 < K) (hy : 0 < y)
    (hN : Tendsto N (𝓝[>] ((5 : ℝ) / 2)) (𝓝 (N ((5 : ℝ) / 2)))) :
    Tendsto (fun r => 2 * 10 ^ 4 * m * K ^ r *
        (m ^ (r - 1) * r ^ ((5 : ℝ) / 2 * r) + r ^ ((3 : ℝ) / 2 * r) * N r) * y ^ (-(r / 2)) + G)
      (𝓝[>] ((5 : ℝ) / 2))
      (𝓝 (2 * 10 ^ 4 * m * K ^ ((5 : ℝ) / 2) *
        (m ^ ((5 : ℝ) / 2 - 1) * ((5 : ℝ) / 2) ^ ((5 : ℝ) / 2 * ((5 : ℝ) / 2)) +
          ((5 : ℝ) / 2) ^ ((3 : ℝ) / 2 * ((5 : ℝ) / 2)) * N ((5 : ℝ) / 2)) *
          y ^ (-(((5 : ℝ) / 2) / 2)) + G)) := by
  have c1 : ContinuousAt (fun r : ℝ => K ^ r) ((5 : ℝ) / 2) := Real.continuousAt_const_rpow hK.ne'
  have c2 : ContinuousAt (fun r : ℝ => m ^ (r - 1)) ((5 : ℝ) / 2) :=
    (Real.continuousAt_const_rpow hm.ne').comp (continuousAt_id.sub continuousAt_const)
  have c3 : ContinuousAt (fun r : ℝ => r ^ ((5 : ℝ) / 2 * r)) ((5 : ℝ) / 2) :=
    continuousAt_id.rpow (continuousAt_const.mul continuousAt_id) (Or.inl (by norm_num))
  have c4 : ContinuousAt (fun r : ℝ => r ^ ((3 : ℝ) / 2 * r)) ((5 : ℝ) / 2) :=
    continuousAt_id.rpow (continuousAt_const.mul continuousAt_id) (Or.inl (by norm_num))
  have c5 : ContinuousAt (fun r : ℝ => y ^ (-(r / 2))) ((5 : ℝ) / 2) :=
    (Real.continuousAt_const_rpow hy.ne').comp (continuousAt_id.div_const 2).neg
  have t := fun {f : ℝ → ℝ} (h : ContinuousAt f ((5 : ℝ) / 2)) =>
    tendsto_nhdsWithin_of_tendsto_nhds (s := Set.Ioi ((5 : ℝ) / 2)) h.tendsto
  refine Tendsto.add ?_ tendsto_const_nhds
  refine Tendsto.mul ?_ (t c5)
  refine Tendsto.mul ((tendsto_const_nhds).mul (t c1)) ?_
  exact ((t c2).mul (t c3)).add ((t c4).mul hN)

/-- Passing from `r > 5/2` to the endpoint `r = 5/2`. -/
lemma endpoint (p : ℝ) (B : ℝ → ℝ) (R : EReal) (hR : (((5 : ℝ) / 2 : ℝ) : EReal) < R)
    (hB : ∀ r : ℝ, (5 : ℝ) / 2 < r → (r : EReal) < R → p ≤ B r)
    (hc : Tendsto B (𝓝[>] ((5 : ℝ) / 2)) (𝓝 (B ((5 : ℝ) / 2)))) :
    ∀ r : ℝ, (5 : ℝ) / 2 ≤ r → (r : EReal) < R → p ≤ B r := by
  intro r hr hrR
  rcases hr.lt_or_eq with hr | hr
  · exact hB r hr hrR
  · subst hr
    obtain ⟨r₀, h1, h2⟩ := EReal.lt_iff_exists_real_btwn.mp hR
    have h1' : (5 : ℝ) / 2 < r₀ := EReal.coe_lt_coe_iff.mp h1
    apply ge_of_tendsto hc
    filter_upwards [Ioo_mem_nhdsGT h1'] with r hr'
    exact hB r hr'.1 (lt_trans (EReal.coe_lt_coe_iff.mpr hr'.2) h2)

/-! ### Numerical inequalities -/

lemma alg_main (r m E R1 R2 Y Y' κ K : ℝ) (hr : 1 ≤ r) (hm : 1 ≤ m) (hE : 0 ≤ E)
    (hR1 : 0 ≤ R1) (hR2 : 0 ≤ R2) (hY : 0 ≤ Y) (hY' : 0 ≤ Y') (hκ : 0 ≤ κ)
    (hYY : Y ≤ κ ^ r * Y') (hK : 92 * 10 ^ 4 * κ ≤ K) :
    13 * 10 ^ 3 * (m + 1) * ((46 : ℝ) * 10 ^ 4) ^ r * ((m + 1) ^ (r - 1) * R1 + R2 * E) * Y ≤
      2 * 10 ^ 4 * m * K ^ r * (m ^ (r - 1) * R1 + R2 * E) * Y' := by
  have hr0 : 0 ≤ r := by linarith
  have hm0 : 0 < m := by linarith
  have hb : (m + 1) ^ (r - 1) ≤ (2 : ℝ) ^ (r - 1) * m ^ (r - 1) := by
    rw [← Real.mul_rpow (by norm_num) hm0.le]
    exact Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
  have h2r : (2 : ℝ) * (2 : ℝ) ^ (r - 1) = (2 : ℝ) ^ r := by
    rw [← Real.rpow_one_add' (by norm_num) (by linarith)]; ring_nf
  have hA : 0 ≤ ((46 : ℝ) * 10 ^ 4) ^ r := by positivity
  have hKr1 : ((92 : ℝ) * 10 ^ 4 * κ) ^ r ≤ K ^ r :=
    Real.rpow_le_rpow (by positivity) hK hr0
  have e1 : ((92 : ℝ) * 10 ^ 4 * κ) ^ r = (2 : ℝ) ^ r * ((46 : ℝ) * 10 ^ 4) ^ r * κ ^ r := by
    rw [show (92 : ℝ) * 10 ^ 4 * κ = 2 * (46 * 10 ^ 4) * κ by ring,
      Real.mul_rpow (by positivity) hκ, Real.mul_rpow (by norm_num) (by norm_num)]
  have h2ge : (2 : ℝ) ≤ (2 : ℝ) ^ r := by
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hr
    simpa using this
  -- first estimate the prefactor
  have step1 : 13 * 10 ^ 3 * (m + 1) * ((46 : ℝ) * 10 ^ 4) ^ r *
      ((m + 1) ^ (r - 1) * R1 + R2 * E) * Y ≤
      13 * 10 ^ 3 * (2 * m) * ((46 : ℝ) * 10 ^ 4) ^ r *
      ((2 : ℝ) ^ (r - 1) * m ^ (r - 1) * R1 + R2 * E) * (κ ^ r * Y') := by
    have h1 : 13 * 10 ^ 3 * (m + 1) * ((46 : ℝ) * 10 ^ 4) ^ r ≤
        13 * 10 ^ 3 * (2 * m) * ((46 : ℝ) * 10 ^ 4) ^ r := by
      apply mul_le_mul_of_nonneg_right _ hA; linarith
    have h2 : (m + 1) ^ (r - 1) * R1 + R2 * E ≤ (2 : ℝ) ^ (r - 1) * m ^ (r - 1) * R1 + R2 * E := by
      have := mul_le_mul_of_nonneg_right hb hR1; linarith
    have hp1 : 0 ≤ (m + 1) ^ (r - 1) * R1 + R2 * E := by positivity
    have hp2 : 0 ≤ 13 * 10 ^ 3 * (2 * m) * ((46 : ℝ) * 10 ^ 4) ^ r := by positivity
    apply mul_le_mul (mul_le_mul h1 h2 hp1 hp2) hYY hY (by positivity)
  refine step1.trans ?_
  -- now compare with `K^r`
  set A := ((46 : ℝ) * 10 ^ 4) ^ r
  set M := m ^ (r - 1)
  set T := (2 : ℝ) ^ r
  set k := κ ^ r
  have hM : 0 ≤ M := by positivity
  have hk : 0 ≤ k := by positivity
  have hKr : T * A * k ≤ K ^ r := by rw [← e1]; exact hKr1
  have e2 : 13 * 10 ^ 3 * (2 * m) * A * ((2 : ℝ) ^ (r - 1) * M * R1 + R2 * E) * (k * Y') =
      13 * 10 ^ 3 * m * (T * A * k) * M * R1 * Y' + 26 * 10 ^ 3 * m * (A * k) * R2 * E * Y' := by
    rw [← h2r]; ring
  have e3 : 2 * 10 ^ 4 * m * K ^ r * (M * R1 + R2 * E) * Y' =
      2 * 10 ^ 4 * m * K ^ r * M * R1 * Y' + 2 * 10 ^ 4 * m * K ^ r * R2 * E * Y' := by ring
  rw [e2, e3]
  have hP1 : 0 ≤ m * M * R1 * Y' := by positivity
  have hP2 : 0 ≤ m * R2 * E * Y' := by positivity
  have hAk : 0 ≤ A * k := by positivity
  have f1 : 13 * 10 ^ 3 * m * (T * A * k) * M * R1 * Y' ≤ 2 * 10 ^ 4 * m * K ^ r * M * R1 * Y' := by
    have : 13 * 10 ^ 3 * (T * A * k) ≤ 2 * 10 ^ 4 * K ^ r := by
      have : 0 ≤ T * A * k := by positivity
      linarith
    have := mul_le_mul_of_nonneg_right this hP1
    linarith [this]
  have f2 : 26 * 10 ^ 3 * m * (A * k) * R2 * E * Y' ≤ 2 * 10 ^ 4 * m * K ^ r * R2 * E * Y' := by
    have h3 : 26 * 10 ^ 3 * (A * k) ≤ 2 * 10 ^ 4 * K ^ r := by
      have : 2 * (A * k) ≤ T * A * k := by
        have := mul_le_mul_of_nonneg_right h2ge hAk
        linarith [this]
      linarith
    have := mul_le_mul_of_nonneg_right h3 hP2
    linarith [this]
  linarith

lemma small_case (r m N R1 R2 y K G : ℝ) (hr : 1 ≤ r) (hm : 1 ≤ m) (hN : 1 ≤ N)
    (hR1 : 0 ≤ R1) (hR2 : 1 ≤ R2) (hy : 0 < y) (hy38 : y ≤ 38) (hK : 38 ≤ K) (hG : 0 ≤ G) :
    1 ≤ 2 * 10 ^ 4 * m * K ^ r * (m ^ (r - 1) * R1 + R2 * N) * y ^ (-(r / 2)) + G := by
  have hr0 : 0 ≤ r := by linarith
  have h1 : (38 : ℝ) ^ (-(r / 2)) ≤ y ^ (-(r / 2)) :=
    Real.rpow_le_rpow_of_nonpos hy hy38 (by linarith)
  have h2 : (1 : ℝ) ≤ K ^ r * (38 : ℝ) ^ (-(r / 2)) := by
    rw [Real.rpow_neg (by norm_num), ← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]
    calc (38 : ℝ) ^ (r / 2) ≤ (38 : ℝ) ^ r :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ ≤ K ^ r := Real.rpow_le_rpow (by norm_num) hK hr0
  have hKy : 1 ≤ K ^ r * y ^ (-(r / 2)) := by
    have : K ^ r * (38 : ℝ) ^ (-(r / 2)) ≤ K ^ r * y ^ (-(r / 2)) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    linarith
  have hM : 0 ≤ m ^ (r - 1) * R1 := by positivity
  have hS : 1 ≤ m ^ (r - 1) * R1 + R2 * N := by nlinarith
  have : 1 ≤ m * (m ^ (r - 1) * R1 + R2 * N) := by nlinarith
  have hpos : 0 ≤ K ^ r * y ^ (-(r / 2)) := by positivity
  have e : 2 * 10 ^ 4 * m * K ^ r * (m ^ (r - 1) * R1 + R2 * N) * y ^ (-(r / 2)) =
      2 * 10 ^ 4 * (m * (m ^ (r - 1) * R1 + R2 * N)) * (K ^ r * y ^ (-(r / 2))) := by ring
  rw [e]
  nlinarith

/-- The algebra for the probability of delay (Li–Goldberg p. 29). -/
lemma delay_alg (n μ' f : ℝ) (hμ : 0 < μ') (hμn : μ' < n) (hf1 : f ≤ (n - μ') / 2)
    (hf2 : (n - μ') / 2 - 1 < f) (hf18 : 18 ≤ f) :
    n * (1 - μ' / n) ^ 2 / 8 ≤ (1 - μ' / (n - f)) * f := by
  have hn : 0 < n := by linarith
  have hd : 36 ≤ n - μ' := by linarith
  have hf4 : (n - μ') / 4 ≤ f := by linarith
  have hnf : (n + μ') / 2 ≤ n - f := by linarith
  have hnf0 : 0 < n - f := by linarith
  have hq : (n - μ') / (n + μ') ≤ 1 - μ' / (n - f) := by
    rw [div_le_iff₀ (by linarith)]
    have : μ' / (n - f) ≤ 2 * μ' / (n + μ') := by
      rw [div_le_div_iff₀ hnf0 (by linarith)]; nlinarith
    have e : (1 - 2 * μ' / (n + μ')) * (n + μ') = n - μ' := by field_simp; ring
    nlinarith [mul_le_mul_of_nonneg_right this (by linarith : (0 : ℝ) ≤ n + μ')]
  have hq0 : 0 ≤ (n - μ') / (n + μ') := div_nonneg (by linarith) (by linarith)
  calc n * (1 - μ' / n) ^ 2 / 8 = (n - μ') ^ 2 / (8 * n) := by field_simp
    _ ≤ (n - μ') / (n + μ') * ((n - μ') / 4) := by
        rw [div_le_iff₀ (by positivity)]
        have e : (n - μ') / (n + μ') * ((n - μ') / 4) * (8 * n) =
            (n - μ') ^ 2 * (2 * n / (n + μ')) := by field_simp; ring
        rw [e]
        have : 1 ≤ 2 * n / (n + μ') := by rw [le_div_iff₀ (by linarith)]; linarith
        nlinarith [sq_nonneg (n - μ')]
    _ ≤ (1 - μ' / (n - f)) * f := mul_le_mul hq hf4 (by linarith) (by linarith [hq0])

end GIGnGoalAux



open GIGnGoalAux in
theorem solution (n : ℕ) (hn : 0 < n) (μA μS : Measure ℝ) [IsProbabilityMeasure μA] [IsProbabilityMeasure μS]
    (hA : IsTimeLaw μA) (hS : IsTimeLaw μS)
    (hA2 : ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂μA < ⊤)
    (hr : (((5 : ℝ) / 2 : ℝ) : EReal) < rStar μS)
    (hstab : rate μA < n * rate μS)
    (π : Measure ℕ) (hπ : IsSteadyStateLaw n μA μS π) :
    (∀ x : ℝ, 0 < x → ∀ r : ℝ, (5 : ℝ) / 2 ≤ r → (r : EReal) < rStar μS →
      π.real {q : ℕ | x / (1 - rho n μA μS) ≤ ((q - n : ℕ) : ℝ)} ≤
        2 * 10 ^ 4 * nMoment μS 2 * ((10 : ℝ) ^ 6) ^ r *
            (nMoment μS 2 ^ (r - 1) * r ^ ((5 : ℝ) / 2 * r) + r ^ ((3 : ℝ) / 2 * r) * nMoment μS r) *
            x ^ (-(r / 2)) +
          11 / 10 * Real.exp (-((225 : ℝ) / 10000) * (nMoment μA 2)⁻¹ * x)) ∧
    (∀ r : ℝ, (5 : ℝ) / 2 ≤ r → (r : EReal) < rStar μS →
      π.real {q : ℕ | n ≤ q} ≤
        2 * 10 ^ 4 * nMoment μS 2 * ((10 : ℝ) ^ 7) ^ r *
            (nMoment μS 2 ^ (r - 1) * r ^ ((5 : ℝ) / 2 * r) + r ^ ((3 : ℝ) / 2 * r) * nMoment μS r) *
            ((n : ℝ) * (1 - rho n μA μS) ^ 2) ^ (-(r / 2)) +
          11 / 10 * Real.exp (-((28 : ℝ) / 10000) * (nMoment μA 2)⁻¹ * n * (1 - rho n μA μS) ^ 2)) := by
  haveI : IsProbabilityMeasure π := hπ.1
  have hμA : 0 < rate μA := inv_pos.mpr hA.mean_pos
  have hc : 0 < rate μS := inv_pos.mpr hS.mean_pos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  -- the rescaled laws (service mean one)
  set c := rate μS with hcdef
  set μA' := μA.map (fun x => c * x) with hμA'
  set μS' := μS.map (fun x => c * x) with hμS'
  haveI : IsProbabilityMeasure μA' := Measure.isProbabilityMeasure_map (meas_mul c).aemeasurable
  haveI : IsProbabilityMeasure μS' := Measure.isProbabilityMeasure_map (meas_mul c).aemeasurable
  have hA' : IsTimeLaw μA' := timeLaw_map μA hA c hc
  have hS' : IsTimeLaw μS' := timeLaw_map μS hS c hc
  have hS1' : mean μS' = 1 := mean_scaled μS hS
  have hmeanS' : ∫ z, z ∂μS' = 1 := hS1'
  have hrateS' : rate μS' = 1 := by rw [rate, hS1']; norm_num
  have hrateA' : rate μA' = c⁻¹ * rate μA := rate_map μA hA c
  have hμ'pos : 0 < rate μA' := by rw [hrateA']; positivity
  have hstab' : rate μA' < n := by
    rw [hrateA', inv_mul_lt_iff₀ hc, mul_comm]; exact hstab
  have hA2' : ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂μA' < ⊤ := lint_sq_map μA hA c hc hA2
  have hrho' : rho n μA' μS' = rho n μA μS := rho_map n μA μS hA hS c hc
  have hrhoval : rho n μA μS = rate μA' / n := by
    rw [← hrho', rho, hrateS', mul_one]
  have hmA : nMoment μA' 2 = nMoment μA 2 := nMoment_map μA hA c hc 2
  have hNr : ∀ p, nMoment μS p = ∫ y, y ^ p ∂μS' := fun p => (int_rpow_map μS hS p).symm
  have hm2 : nMoment μS 2 = ∫ y, y ^ 2 ∂μS' := (int_sq_map μS hS).symm
  have hrStar : rStar μS ≤ rStar μS' := rStar_map μS hS c hc
  set ρ := rho n μA μS with hρdef
  have hρ0 : 0 < ρ := by rw [hrhoval]; positivity
  have hρ1 : ρ < 1 := by rw [hrhoval, div_lt_one hn0]; exact hstab'
  -- finiteness of moments of the rescaled service law
  have hfin : ∀ p : ℝ, 0 ≤ p → (p : EReal) < rStar μS → ∫⁻ x, ENNReal.ofReal (x ^ p) ∂μS' < ⊤ := by
    intro p hp hpr
    unfold rStar at hpr
    obtain ⟨b, ⟨p₁, ⟨_, hp₁fin⟩, rfl⟩, hpb⟩ := lt_sSup_iff.mp hpr
    have h1 := moment_fin μS hS.nonneg p p₁ hp (EReal.coe_lt_coe_iff.mp hpb).le hp₁fin
    rw [hμS', lint_rpow_map μS hS c hc p hp]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top h1
  -- an exponent `r₀ > 5/2` with a finite moment
  obtain ⟨r₀, hr₀a, hr₀b⟩ := EReal.lt_iff_exists_real_btwn.mp hr
  have hr₀ : (5 : ℝ) / 2 < r₀ := EReal.coe_lt_coe_iff.mp hr₀a
  have hr₀fin := hfin r₀ (by linarith) hr₀b
  -- moments are at least one
  have hm1 : 1 ≤ nMoment μS 2 := by
    have := one_le_moment μS' hS' hmeanS' 2 (by norm_num) (hfin 2 (by norm_num)
      (lt_of_le_of_lt (EReal.coe_le_coe_iff.mpr (by norm_num)) hr))
    rw [hm2]; simpa [Real.rpow_two] using this
  have hm0 : 0 < nMoment μS 2 := by linarith
  have hNge : ∀ p : ℝ, 1 ≤ p → (p : EReal) < rStar μS → 1 ≤ nMoment μS p := by
    intro p hp hpr
    rw [hNr]; exact one_le_moment μS' hS' hmeanS' p hp (hfin p (by linarith) hpr)
  -- right-continuity of `r ↦ E[(Sμ_S)^r]`
  have hNtend : Tendsto (fun p => nMoment μS p) (𝓝[>] ((5 : ℝ) / 2))
      (𝓝 (nMoment μS ((5 : ℝ) / 2))) := by
    simp_rw [hNr]
    exact moment_tendsto μS' hS' _ r₀ (by norm_num) hr₀ hr₀fin
  have hmAinv : 0 ≤ (nMoment μA 2)⁻¹ := by
    apply inv_nonneg.mpr
    apply integral_nonneg
    intro y
    show (0 : ℝ) ≤ (y * rate μA) ^ (2 : ℝ)
    rw [Real.rpow_two]; positivity
  have hR2 : ∀ p : ℝ, 1 ≤ p → 1 ≤ p ^ ((3 : ℝ) / 2 * p) := fun p hp =>
    Real.one_le_rpow hp (by positivity)
  have hπle : ∀ s : Set ℕ, π.real s ≤ 1 := fun s => measureReal_le_one
  constructor
  · ------------------------------------------------------------------ tail bound
    intro x hx r hr1 hr2
    set X := x / (1 - ρ) with hXdef
    have h1ρ : 0 < 1 - ρ := by linarith
    have hX : 0 < X := div_pos hx h1ρ
    have hXx : (1 - ρ) * X = x := by rw [hXdef]; field_simp
    -- the bounding family and its rescaling
    let F := canonFamily n μA μS hA hS
    let F' := scaleFamily hA hS F c hc
    have hL1 := GIGnBounds.Tail.lemma_1 n hn μA μS hA hS hstab π hπ _ (canonP n μA μS hA hS) F X hX
    by_cases hX18 : 18 ≤ X
    · -- large `X`: Lemma 1 + the bound on the supremum for every `r > 5/2`
      have hB : ∀ r' : ℝ, (5 : ℝ) / 2 < r' → (r' : EReal) < rStar μS →
          π.real {q : ℕ | X ≤ ((q - n : ℕ) : ℝ)} ≤
            2 * 10 ^ 4 * nMoment μS 2 * ((10 : ℝ) ^ 6) ^ r' *
              (nMoment μS 2 ^ (r' - 1) * r' ^ ((5 : ℝ) / 2 * r') +
                r' ^ ((3 : ℝ) / 2 * r') * nMoment μS r') * x ^ (-(r' / 2)) +
            11 / 10 * Real.exp (-((225 : ℝ) / 10000) * (nMoment μA 2)⁻¹ * x) := by
        intro r' hr'1 hr'2
        have hsb := GIGnBounds.Tail.sup_bound_r_gt_2_5 n hn μA' μS' hA' hS' hS1' hstab' hA2' _
          (canonP n μA μS hA hS) F' r' hr'1 (lt_of_lt_of_le hr'2 hrStar) X hX18
        have hsets : {ω | (X : EReal) ≤ supFrom (fun t => (F'.Ae ω t : ℝ) - ∑ i, (F'.Ne i ω t : ℝ))}
            = {ω | (X : EReal) ≤ supFrom (fun t => (F.Ae ω t : ℝ) - ∑ i, (F.Ne i ω t : ℝ))} := by
          ext ω; simp only [Set.mem_setOf_eq]; rw [scale_sup hA hS F c hc ω]
        rw [hsets, hrho', hXx, hmA, ← hm2, ← hNr r'] at hsb
        refine hL1.trans (hsb.trans ?_)
        have hY : 0 ≤ x ^ (-(r' / 2)) := by positivity
        have halg := alg_main r' (nMoment μS 2) (nMoment μS r') (r' ^ ((5 : ℝ) / 2 * r'))
          (r' ^ ((3 : ℝ) / 2 * r')) (x ^ (-(r' / 2))) (x ^ (-(r' / 2))) 1 ((10 : ℝ) ^ 6)
          (by linarith) hm1 (by linarith [hNge r' (by linarith) hr'2]) (by positivity)
          (by positivity) hY hY (by norm_num) (by rw [Real.one_rpow, one_mul]) (by norm_num)
        linarith
      have hcont := bound_tendsto (nMoment μS 2) ((10 : ℝ) ^ 6) x
        (11 / 10 * Real.exp (-((225 : ℝ) / 10000) * (nMoment μA 2)⁻¹ * x))
        (fun p => nMoment μS p) hm0 (by positivity) hx hNtend
      exact endpoint _ _ (rStar μS) hr hB hcont r hr1 hr2
    · -- small `X`: the bound is at least one
      push Not at hX18
      have hx18 : x ≤ 38 := by
        have : x = (1 - ρ) * X := hXx.symm
        nlinarith
      refine (hπle _).trans ?_
      exact small_case r (nMoment μS 2) (nMoment μS r) (r ^ ((5 : ℝ) / 2 * r))
        (r ^ ((3 : ℝ) / 2 * r)) x ((10 : ℝ) ^ 6) _ (by linarith) hm1 (hNge r (by linarith) hr2)
        (by positivity) (hR2 r (by linarith)) hx hx18 (by norm_num) (by positivity)
  · ------------------------------------------------------------------ probability of delay
    intro r hr1 hr2
    set μ' := rate μA' with hμ'def
    set f := ⌊(1 / 2 : ℝ) * (n - μ')⌋₊ with hfdef
    have hf1 : (f : ℝ) ≤ (n - μ') / 2 := by
      have := Nat.floor_le (show (0 : ℝ) ≤ (1 / 2 : ℝ) * (n - μ') by nlinarith)
      linarith
    have hf2 : (n - μ') / 2 - 1 < (f : ℝ) := by
      have := Nat.lt_floor_add_one ((1 / 2 : ℝ) * (n - μ'))
      linarith
    have hfn : f < n := by
      have : (f : ℝ) < n := by linarith
      exact_mod_cast this
    have hn'1 : 1 ≤ n - f := by omega
    have hcast : ((n - f : ℕ) : ℝ) = (n : ℝ) - f := Nat.cast_sub hfn.le
    have hw : (n : ℝ) * (1 - ρ) ^ 2 = (n - μ') ^ 2 / n := by
      rw [hrhoval]; field_simp
    have hwpos : 0 < (n : ℝ) * (1 - ρ) ^ 2 := by
      have : 0 < 1 - ρ := by linarith
      positivity
    -- Lemma 7 with `n' = n - f` and `x = 0`
    let F2 := canonFamily (n - f) μA μS hA hS
    let F2' := scaleFamily hA hS F2 c hc
    have hL7 := GIGnBounds.Tail.lemma_7 n hn μA μS hA hS hstab π hπ (n - f) hn'1 (Nat.sub_le n f) 0
      (by rw [hcast]; simp) _ (canonP (n - f) μA μS hA hS) F2
    have hset : {q : ℕ | n ≤ q} = {q : ℕ | (0 : ℝ) ≤ (q : ℝ) - n} := by
      ext q; simp only [Set.mem_setOf_eq, sub_nonneg, Nat.cast_le]
    have hthr : ((0 + ((n : ℝ) - ((n - f : ℕ) : ℝ)) : ℝ) : EReal) = ((f : ℝ) : EReal) := by
      rw [hcast]; congr 1; ring
    rw [hthr, ← hset] at hL7
    by_cases hf18 : (18 : ℝ) ≤ f
    · have hB : ∀ r' : ℝ, (5 : ℝ) / 2 < r' → (r' : EReal) < rStar μS →
          π.real {q : ℕ | n ≤ q} ≤
            2 * 10 ^ 4 * nMoment μS 2 * ((10 : ℝ) ^ 7) ^ r' *
              (nMoment μS 2 ^ (r' - 1) * r' ^ ((5 : ℝ) / 2 * r') +
                r' ^ ((3 : ℝ) / 2 * r') * nMoment μS r') *
              ((n : ℝ) * (1 - ρ) ^ 2) ^ (-(r' / 2)) +
            11 / 10 * Real.exp (-((28 : ℝ) / 10000) * (nMoment μA 2)⁻¹ * n * (1 - ρ) ^ 2) := by
        intro r' hr'1 hr'2
        have hstab'' : rate μA' < ((n - f : ℕ) : ℝ) := by rw [hcast]; linarith
        have hsb := GIGnBounds.Tail.sup_bound_r_gt_2_5 (n - f) hn'1 μA' μS' hA' hS' hS1' hstab''
          hA2' _ (canonP (n - f) μA μS hA hS) F2' r' hr'1 (lt_of_lt_of_le hr'2 hrStar) f hf18
        have hsets : {ω | ((f : ℝ) : EReal) ≤
            supFrom (fun t => (F2'.Ae ω t : ℝ) - ∑ i, (F2'.Ne i ω t : ℝ))} =
            {ω | ((f : ℝ) : EReal) ≤
              supFrom (fun t => (F2.Ae ω t : ℝ) - ∑ i, (F2.Ne i ω t : ℝ))} := by
          ext ω; simp only [Set.mem_setOf_eq]; rw [scale_sup hA hS F2 c hc ω]
        have hrho2 : rho (n - f) μA' μS' = μ' / ((n : ℝ) - f) := by
          rw [rho, hrateS', mul_one, hcast]
        rw [hsets, hrho2, hmA, ← hm2, ← hNr r'] at hsb
        refine hL7.trans (hsb.trans ?_)
        -- the algebra of p. 29
        set z := (1 - μ' / ((n : ℝ) - f)) * f with hz
        set w := (n : ℝ) * (1 - ρ) ^ 2 with hwdef
        have hzw : w / 8 ≤ z := by
          rw [hwdef, hrhoval]
          exact delay_alg n μ' f hμ'pos hstab' hf1 hf2 hf18
        have hw8 : 0 < w / 8 := by positivity
        set κ := (8 : ℝ) ^ ((1 : ℝ) / 2) with hκ
        have hκ0 : 0 ≤ κ := by positivity
        have hκ3 : κ ≤ 3 := by
          have : (3 : ℝ) = (9 : ℝ) ^ ((1 : ℝ) / 2) := by
            rw [show (9 : ℝ) = 3 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
          rw [this]
          exact Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
        have hYY : z ^ (-(r' / 2)) ≤ κ ^ r' * w ^ (-(r' / 2)) := by
          have h1 : z ^ (-(r' / 2)) ≤ (w / 8) ^ (-(r' / 2)) :=
            Real.rpow_le_rpow_of_nonpos hw8 hzw (by linarith)
          have h2 : (w / 8) ^ (-(r' / 2)) = κ ^ r' * w ^ (-(r' / 2)) := by
            rw [Real.div_rpow hwpos.le (by norm_num), hκ, ← Real.rpow_mul (by norm_num),
              Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 8)]
            field_simp
          linarith
        have hzpos : 0 < z := lt_of_lt_of_le hw8 hzw
        have halg := alg_main r' (nMoment μS 2) (nMoment μS r') (r' ^ ((5 : ℝ) / 2 * r'))
          (r' ^ ((3 : ℝ) / 2 * r')) (z ^ (-(r' / 2))) (w ^ (-(r' / 2))) κ ((10 : ℝ) ^ 7)
          (by linarith) hm1 (by linarith [hNge r' (by linarith) hr'2]) (by positivity)
          (by positivity) (by positivity) (by positivity) hκ0 hYY (by norm_num; linarith)
        have hexp : Real.exp (-((225 : ℝ) / 10000) * (nMoment μA 2)⁻¹ * z) ≤
            Real.exp (-((28 : ℝ) / 10000) * (nMoment μA 2)⁻¹ * n * (1 - ρ) ^ 2) := by
          apply Real.exp_le_exp.mpr
          have e : -((28 : ℝ) / 10000) * (nMoment μA 2)⁻¹ * n * (1 - ρ) ^ 2 =
              -((28 : ℝ) / 10000) * (nMoment μA 2)⁻¹ * w := by rw [hwdef]; ring
          rw [e]
          have : (28 : ℝ) / 10000 * w ≤ (225 : ℝ) / 10000 * z := by linarith
          have h3 := mul_le_mul_of_nonneg_left this hmAinv
          have e1 : -((225 : ℝ) / 10000) * (nMoment μA 2)⁻¹ * z =
              -((nMoment μA 2)⁻¹ * ((225 : ℝ) / 10000 * z)) := by ring
          have e2 : -((28 : ℝ) / 10000) * (nMoment μA 2)⁻¹ * w =
              -((nMoment μA 2)⁻¹ * ((28 : ℝ) / 10000 * w)) := by ring
          rw [e1, e2]
          linarith
        linarith
      have hcont := bound_tendsto (nMoment μS 2) ((10 : ℝ) ^ 7) ((n : ℝ) * (1 - ρ) ^ 2)
        (11 / 10 * Real.exp (-((28 : ℝ) / 10000) * (nMoment μA 2)⁻¹ * n * (1 - ρ) ^ 2))
        (fun p => nMoment μS p) hm0 (by positivity) hwpos hNtend
      exact endpoint _ _ (rStar μS) hr hB hcont r hr1 hr2
    · push Not at hf18
      have hw38 : (n : ℝ) * (1 - ρ) ^ 2 ≤ 38 := by
        rw [hw]
        have hd : 0 < (n : ℝ) - μ' := by linarith
        have hd38 : (n : ℝ) - μ' < 38 := by linarith
        rw [div_le_iff₀ hn0, sq]
        have := mul_le_mul_of_nonneg_left hd38.le hd.le
        linarith
      refine (hπle _).trans ?_
      have hr1' : (1 : ℝ) ≤ r := by linarith
      exact small_case r (nMoment μS 2) (nMoment μS r) (r ^ ((5 : ℝ) / 2 * r))
        (r ^ ((3 : ℝ) / 2 * r)) ((n : ℝ) * (1 - ρ) ^ 2) ((10 : ℝ) ^ 7)
        (11 / 10 * Real.exp (-((28 : ℝ) / 10000) * (nMoment μA 2)⁻¹ * n * (1 - ρ) ^ 2))
        hr1' hm1 (hNge r hr1' hr2)
        (by positivity) (hR2 r hr1') hwpos hw38 (by norm_num) (by positivity)
